import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformSchwartzSeminormBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmittedFormEqAdelicThetaDistribution
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvIInfScaleMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPointwiseArchimedeanDecayBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicThetaSumNormLePolynomialScale
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalDarbouxHermitianTensorAdeles
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusElementActsOnFrameColumns
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSchwartzThetaDistributionSumNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordsGoodModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenBijectiveSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenSchwartzSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusActionModelCoordinates
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFixedBySmallHeisenbergLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsScaleMovedHeisenbergLatticePolynomialHeighStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundedDenominatorStandardCharTrivialStatement

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniform_schwartz_seminorm_bound : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (I : Type)
    (lam : I → SchwartzMap V ℂ →L[ℂ] ℂ) (w : I → ℝ), (∀ i, 0 ≤ w i) →
    (∀ f, ∃ (N : ℕ) (C : ℝ), ∀ i, ‖lam i f‖ ≤ C * w i ^ N) →
    ∃ (N : ℕ) (C : ℝ) (T : Finset (ℕ × ℕ)), ∀ i f, ‖lam i f‖ ≤ C * (T.sup (schwartzSeminormFamily ℂ V ℂ)) f * w i ^ N := by
  first | exact @GlobalTheory.schwartz_family_uniform_bound | exact GlobalTheory.schwartz_family_uniform_bound | (intros; apply GlobalTheory.schwartz_family_uniform_bound <;> assumption)
end

section
section
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

noncomputable section

namespace GlobalTheory.ThetaKernelCont

theorem theta_pureA_clm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ φ ∈ SB (Fin n × Fin d → Af F), ∀ (g : UA σ X.J) (h : UA σ W.J),
    ∃ T : SInf F (Fin n × Fin d) →L[ℂ] ℂ, ∀ f : SInf F (Fin n × Fin d), theta om (pureA F f φ) g h = T f := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP φ hφ g h
  obtain ⟨l, hl, hlθ⟩ := GlobalTheory.ThetaAdmitted.exists_admitted_form_eq_adelicThetaDistribution_alt F (Fin n × Fin d)
  have hs := hP.weil.isUSplitting
  obtain ⟨T, hT⟩ := hs.adm (g, h) l hl φ hφ
  refine ⟨T, fun f => ?_⟩
  have hmem : pureA F f φ ∈ schA F (Fin n × Fin d) := Submodule.subset_span ⟨f, φ, hφ, rfl⟩
  have hmem' : om (g, h) (pureA F f φ) ∈ schA F (Fin n × Fin d) := hs.pres (g, h) _ hmem
  rw [← hT f, LinearMap.comp_apply, hlθ _ hmem']
  rfl

end GlobalTheory.ThetaKernelCont
end
end

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_kernel_continuous_functional : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ φ ∈ SB (Fin n × Fin d → Af F), ∀ (g : UA σ X.J) (h : UA σ W.J),
    ∃ T : SInf F (Fin n × Fin d) →L[ℂ] ℂ, ∀ f : SInf F (Fin n × Fin d), theta om (pureA F f φ) g h = T f := by
  atlas_forward_decl GlobalTheory.ThetaKernelCont.theta_pureA_clm
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.PairCoords

def pairBil {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (c : S →ₐ[R] S) {d : ℕ}
    (K : Matrix (Fin d) (Fin d) S) : LinearMap.BilinForm R (Fin d → S) :=
  LinearMap.mk₂ R (fun b a => Algebra.trace R S (-∑ j, ∑ l, b j * K j l * c (a l)))
    (fun b b' a => by
      simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, neg_add, map_add])
    (fun r b a => by
      simp only [Pi.smul_apply, smul_mul_assoc, ← Finset.smul_sum, ← smul_neg, map_smul, smul_eq_mul])
    (fun b a a' => by
      simp only [Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib, neg_add])
    (fun r b a => by
      simp only [Pi.smul_apply, map_smul, mul_smul_comm, ← Finset.smul_sum, ← smul_neg, smul_eq_mul])

theorem pairBil_apply {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (c : S →ₐ[R] S) {d : ℕ}
    (K : Matrix (Fin d) (Fin d) S) (b a : Fin d → S) :
    pairBil c K b a = Algebra.trace R S (-∑ j, ∑ l, b j * K j l * c (a l)) := rfl

section Field

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] [CharZero F]

theorem eq_zero_of_pairBil (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {d : ℕ} {K : Matrix (Fin d) (Fin d) E}
    (hK : K.det ≠ 0) (b : Fin d → E) (hb : ∀ a, pairBil σ K b a = 0) : b = 0 := by
  have h1 : b ᵥ* K = 0 := by
    funext l
    refine (traceForm_nondegenerate F E).1 _ fun e => ?_
    have := hb (Pi.single l (σ (-e)) : Fin d → E)
    rw [pairBil_apply] at this
    rw [Algebra.traceForm_apply, ← this]
    congr 1
    have hs : ∀ j, ∑ l', b j * K j l' * σ ((Pi.single l (σ (-e)) : Fin d → E) l') = b j * K j l * -e := fun j => by
      rw [Finset.sum_eq_single l]
      · simp [hσ]
      · intro l' _ h
        simp [Pi.single_apply, h]
      · simp
    simp only [hs, Matrix.vecMul, dotProduct, Pi.zero_apply, Finset.sum_mul]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  calc b = b ᵥ* (K * K⁻¹) := by rw [Matrix.mul_nonsing_inv _ (Ne.isUnit hK), Matrix.vecMul_one]
    _ = (b ᵥ* K) ᵥ* K⁻¹ := (Matrix.vecMul_vecMul _ _ _).symm
    _ = 0 := by rw [h1, Matrix.zero_vecMul]

theorem nondegenerate_pairBil (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {d : ℕ} {K : Matrix (Fin d) (Fin d) E}
    (hK : K.det ≠ 0) : (pairBil σ K).Nondegenerate :=
  LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft (fun b hb => eq_zero_of_pairBil σ hσ hK b hb)

end Field

end GlobalTheory.PairCoords

namespace GlobalTheory.PairCoords

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem trace_inclR (e : E) : Algebra.trace (AF F) (AE F E) (inclR (F := F) (AF F) e) =
    algebraMap F (AF F) (Algebra.trace F E e) := by
  show Algebra.trace (AF F) (AF F ⊗[F] E) ((1 : AF F) ⊗ₜ[F] e) = _
  rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]

theorem pairBil_incV (σ : E →ₐ[F] E) {d : ℕ} (K : Matrix (Fin d) (Fin d) E) (v w : Fin d → E) :
    pairBil (cA σ) (incM F K) (incV F v) (incV F w) = algebraMap F (AF F) (pairBil σ K v w) := by
  have hc : ∀ e : E, cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := fun e => rfl
  rw [pairBil_apply, pairBil_apply, ← trace_inclR]
  simp only [incV, incM, Matrix.map_apply, hc, map_mul, map_sum, map_neg]

theorem cA_cA (σ : E →ₐ[F] E) (hσ : ∀ a, σ (σ a) = a) (x : AE F E) : cA σ (cA σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [cA, hσ]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

end GlobalTheory.PairCoords

theorem GlobalTheory.PairCoords.exists_pair_coords : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ)
    (K : Matrix (Fin d) (Fin d) E), (∀ a, σ (σ a) = a) → Module.finrank F E = 2 → (∀ i j, σ (K j i) = -K i j) → K.det ≠ 0 →
    ∃ p q : (Fin d → AE F E) ≃ₗ[AF F] (Fin 2 × Fin d → AF F),
      (∀ a b, q b ⬝ᵥ p a = Algebra.trace (AF F) (AE F E) (-∑ j, ∑ l, b j * incM F K j l * cA σ (a l))) ∧
      (∀ a b, q b ⬝ᵥ p a = Algebra.trace (AF F) (AE F E) (∑ j, ∑ l, a j * incM F K j l * cA σ (b l))) ∧
      (∀ a : Fin d → E, ∃ y : Fin 2 × Fin d → F, p (incV F a) = fun k => algebraMap F (AF F) (y k)) ∧
      (∀ a : Fin d → E, ∃ y : Fin 2 × Fin d → F, q (incV F a) = fun k => algebraMap F (AF F) (y k)) := by
  intro F E _ _ _ _ _ σ d K hσ h2 hK hdet
  classical
  have hrk : Module.finrank F (Fin d → E) = 2 * d := by
    rw [Module.finrank_pi_fintype]
    simp [h2, mul_comm]
  let β : Module.Basis (Fin 2 × Fin d) F (Fin d → E) :=
    (Module.finBasisOfFinrankEq F (Fin d → E) hrk).reindex finProdFinEquiv.symm
  let hnd := GlobalTheory.PairCoords.nondegenerate_pairBil σ hσ hdet
  let β₂ := (GlobalTheory.PairCoords.pairBil σ K).dualBasis hnd β
  let e := TensorProduct.piRight F (AF F) (AF F) (fun _ : Fin d => E)
  have hinc : ∀ v : Fin d → E, e ((1 : AF F) ⊗ₜ[F] v) = incV F v := fun v => by
    funext i
    rfl
  let B₁ := (β.baseChange (AF F)).map e
  let B₂ := (β₂.baseChange (AF F)).map e
  have hB₁ : ∀ l, B₁ l = incV F (β l) := fun l => by
    simp only [B₁, Module.Basis.map_apply, Module.Basis.baseChange_apply, hinc]
  have hB₂ : ∀ l, B₂ l = incV F (β₂ l) := fun l => by
    simp only [B₂, Module.Basis.map_apply, Module.Basis.baseChange_apply, hinc]
  have hk : ∀ k l, GlobalTheory.PairCoords.pairBil (cA σ) (incM F K) (B₂ k) (B₁ l) = if l = k then 1 else 0 := by
    intro k l
    rw [hB₁, hB₂, GlobalTheory.PairCoords.pairBil_incV, LinearMap.BilinForm.apply_dualBasis_left]
    split_ifs <;> simp
  have h1 : ∀ a b, B₂.equivFun b ⬝ᵥ B₁.equivFun a =
      Algebra.trace (AF F) (AE F E) (-∑ j, ∑ l, b j * incM F K j l * cA σ (a l)) := by
    intro a b
    rw [← GlobalTheory.PairCoords.pairBil_apply]
    conv_rhs => rw [← B₂.sum_equivFun b, ← B₁.sum_equivFun a]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hk, smul_eq_mul, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, dotProduct]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hcc := GlobalTheory.PairCoords.cA_cA σ hσ
  have hK' : ∀ j l, cA σ (incM F K j l) = -incM F K l j := fun j l => by
    show inclR (F := F) (AF F) (σ (K j l)) = -inclR (F := F) (AF F) (K l j)
    rw [hK l j, map_neg]
  have h2' : ∀ a b : Fin d → AE F E, Algebra.trace (AF F) (AE F E) (-∑ j, ∑ l, b j * incM F K j l * cA σ (a l)) =
      Algebra.trace (AF F) (AE F E) (∑ j, ∑ l, a j * incM F K j l * cA σ (b l)) := by
    intro a b
    let eA : AE F E ≃ₐ[AF F] AE F E := AlgEquiv.ofBijective (cA σ) (Function.Involutive.bijective hcc)
    rw [← Algebra.trace_eq_of_algEquiv eA (∑ j, ∑ l, a j * incM F K j l * cA σ (b l))]
    congr 1
    show _ = cA σ _
    simp only [map_sum, map_mul, hcc, hK', ← Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  have hrat : ∀ (b : Module.Basis (Fin 2 × Fin d) F (Fin d → E)) (a : Fin d → E),
      ((b.baseChange (AF F)).map e).equivFun (incV F a) = fun k => algebraMap F (AF F) (b.repr a k) := by
    intro b a
    funext k
    rw [← hinc, Module.Basis.equivFun_apply, Module.Basis.map_repr, LinearEquiv.trans_apply,
      LinearEquiv.symm_apply_apply, Module.Basis.baseChange_repr_tmul, Algebra.algebraMap_eq_smul_one]
  exact ⟨B₁.equivFun, B₂.equivFun, h1, fun a b => (h1 a b).trans (h2' a b),
    fun a => ⟨_, hrat β a⟩, fun a => ⟨_, hrat β₂ a⟩⟩
end
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quadratic_extension_symplectic_coordinates : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ)
    (K : Matrix (Fin d) (Fin d) E), (∀ a, σ (σ a) = a) → Module.finrank F E = 2 → (∀ i j, σ (K j i) = -K i j) → K.det ≠ 0 →
    ∃ p q : (Fin d → AE F E) ≃ₗ[AF F] (Fin 2 × Fin d → AF F),
      (∀ a b, q b ⬝ᵥ p a = Algebra.trace (AF F) (AE F E) (-∑ j, ∑ l, b j * incM F K j l * cA σ (a l))) ∧
      (∀ a b, q b ⬝ᵥ p a = Algebra.trace (AF F) (AE F E) (∑ j, ∑ l, a j * incM F K j l * cA σ (b l))) ∧
      (∀ a : Fin d → E, ∃ y : Fin 2 × Fin d → F, p (incV F a) = fun k => algebraMap F (AF F) (y k)) ∧
      (∀ a : Fin d → E, ∃ y : Fin 2 × Fin d → F, q (incV F a) = fun k => algebraMap F (AF F) (y k)) := by
  first | exact @GlobalTheory.PairCoords.exists_pair_coords | exact GlobalTheory.PairCoords.exists_pair_coords | (intros; apply GlobalTheory.PairCoords.exists_pair_coords <;> assumption)
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory

theorem hTens_eq_trace {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (c : S →ₐ[R] S)
    {α β : Type} [Fintype α] [Fintype β] (JA : Matrix α α S) (JB : Matrix β β S) (x y : Matrix α β S) :
    hTens c JA JB x y = Matrix.trace (JAᵀ * (x * JB * (y.map c)ᵀ)) := by
  simp only [hTens, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => enter [2, k]; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

theorem symp_mul_left {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (c : S →ₐ[R] S) (ξ : S)
    {α α' β : Type} [Fintype α] [Fintype α'] [Fintype β]
    (JA : Matrix α α S) (JB : Matrix β β S) (P : Matrix α α' S) (z z' : Matrix α' β S) :
    symp c ξ JA JB (P * z) (P * z') = symp c ξ (Pᵀ * JA * P.map c) JB z z' := by
  unfold symp
  congr 2
  rw [hTens_eq_trace, hTens_eq_trace, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_mul, Matrix.transpose_transpose]
  simp only [Matrix.mul_assoc]
  conv_rhs => rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

end GlobalTheory
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplectic_form_base_change_matrix : ∀ {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (c : S →ₐ[R] S) (ξ : S) {α α' β : Type} [Fintype α] [Fintype α'] [Fintype β]
    (JA : Matrix α α S) (JB : Matrix β β S) (P : Matrix α α' S) (z z' : Matrix α' β S),
    symp c ξ JA JB (P * z) (P * z') = symp c ξ (Pᵀ * JA * P.map c) JB z z' := by
  first | exact @GlobalTheory.symp_mul_left | exact GlobalTheory.symp_mul_left | (intros; apply GlobalTheory.symp_mul_left <;> assumption)
end

section
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_element_acts_on_frame_columns : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r₀ : ℕ) (Xf Yf : Matrix (Fin n) (Fin r₀) E)
    (t : Fin r₀ → ℝ), (∀ i, 0 < t i) → ∀ a, GlobalTheory.SiegelSet.IsTorusElt σ J Xf Yf t a →
    ((HA.mat (AF F) σ J a : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) * incM F Xf =
        incM F Xf * Matrix.diagonal (fun i => algebraMap (AF F) (AE F E) (GlobalTheory.TorusTheta.infScale F (t i))) ∧
      ((HA.mat (AF F) σ J a : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) * incM F Yf =
        incM F Yf * Matrix.diagonal (fun i => algebraMap (AF F) (AE F E) (GlobalTheory.TorusTheta.infScale F (t i)⁻¹)) ∧
      ∀ z : Fin n → E, (Formalism.UG.cT (σ : E →+* E) Xf * J) *ᵥ z = 0 → (Formalism.UG.cT (σ : E →+* E) Yf * J) *ᵥ z = 0 →
        ((HA.mat (AF F) σ J a : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) *ᵥ
          (fun i => inclR (F := F) (AF F) (z i)) = fun i => inclR (F := F) (AF F) (z i) := by
  first | exact @GlobalTheory.TorusMat.isTorusElt_mat | exact GlobalTheory.TorusMat.isTorusElt_mat | (intros; apply GlobalTheory.TorusMat.isTorusElt_mat <;> assumption)
end

section
section
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

namespace GlobalTheory.SiegelSet.PerpBasis

theorem exists_ker_basis {E : Type} [Field E] {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι (Fin n) E) (B : Matrix (Fin n) ι E) (h : G * B * (G * B) = 1) :
    ∃ (n₀ : ℕ) (Z : Matrix (Fin n) (Fin n₀) E) (Q : Matrix (Fin n₀ ⊕ ι) (Fin n) E),
      n₀ + Fintype.card ι = n ∧ Q * Matrix.fromCols Z B = 1 ∧ Matrix.fromCols Z B * Q = 1 ∧ G * Z = 0 := by
  set K := LinearMap.ker G.mulVecLin with hK
  let b := Module.finBasis E K
  let Z : Matrix (Fin n) (Fin (Module.finrank E K)) E := Matrix.of fun i j => (b j : Fin n → E) i
  have hZv : ∀ a, Z *ᵥ a = ((∑ j, a j • b j : K) : Fin n → E) := by
    intro a
    ext i
    simp [Z, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hGZv : ∀ a, G *ᵥ (Z *ᵥ a) = 0 := by
    intro a
    rw [hZv]
    exact (∑ j, a j • b j : K).2
  have hGZ : G * Z = 0 := by
    ext i j
    have := congrFun (hGZv (Pi.single j 1)) i
    rw [Matrix.mulVec_mulVec] at this
    simpa using this
  have hsurj : LinearMap.range G.mulVecLin = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro v
    refine ⟨(B * (G * B)) *ᵥ v, ?_⟩
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
    rw [← Matrix.mul_assoc, h, Matrix.one_mulVec]
  have hdim : Module.finrank E K + Fintype.card ι = n := by
    have := LinearMap.finrank_range_add_finrank_ker G.mulVecLin
    rw [hsurj] at this
    simp only [finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at this
    rw [hK]
    omega
  have hinj : Function.Injective (Matrix.toLin' (Matrix.fromCols Z B)) := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    rw [Matrix.toLin'_apply, Matrix.fromCols_mulVec] at hv
    have h1 : (G * B) *ᵥ (v ∘ Sum.inr) = 0 := by
      have := congrArg (G *ᵥ ·) hv
      simp only [Matrix.mulVec_add, hGZv, zero_add, Matrix.mulVec_zero] at this
      rw [← Matrix.mulVec_mulVec]; exact this
    have h2 : v ∘ Sum.inr = 0 := by
      have := congrArg ((G * B) *ᵥ ·) h1
      simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at this
      rwa [h, Matrix.one_mulVec] at this
    rw [h2, Matrix.mulVec_zero, add_zero, hZv] at hv
    have h3 : (∑ j, (v ∘ Sum.inl) j • b j : K) = 0 := Subtype.ext hv
    have h4 := Fintype.linearIndependent_iff.1 b.linearIndependent _ h3
    ext x
    rcases x with x | x
    · exact h4 x
    · exact congrFun h2 x
  let e := LinearMap.linearEquivOfInjective _ hinj (by simp [hdim])
  have he : (e : (Fin (Module.finrank E K) ⊕ ι → E) →ₗ[E] (Fin n → E)) =
      Matrix.toLin' (Matrix.fromCols Z B) := by
    ext1 x; rfl
  have he' : LinearMap.toMatrix' (e : (Fin (Module.finrank E K) ⊕ ι → E) →ₗ[E] (Fin n → E)) =
      Matrix.fromCols Z B := by rw [he, LinearMap.toMatrix'_toLin']
  refine ⟨_, Z, LinearMap.toMatrix' (e.symm : (Fin n → E) →ₗ[E] (Fin (Module.finrank E K) ⊕ ι → E)),
    hdim, ?_, ?_, hGZ⟩
  · rw [← he', ← LinearMap.toMatrix'_comp]; simp
  · rw [← he', ← LinearMap.toMatrix'_comp]; simp

section
variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)

theorem gram_eq_map (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {a b : Type}
    (A : Matrix (Fin n) a E) (B : Matrix (Fin n) b E) :
    Aᵀ * J * B.map σ = (Formalism.UG.cT (σ : E →+* E) A * ((1 : E) • J.map σ) * B).map σ := by
  ext i j
  simp [Formalism.UG.cT, Matrix.mul_apply, hσ]

theorem gram_eq_transpose {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (hJ : ∀ i j, σ (J j i) = J i j)
    {a b : Type} (A : Matrix (Fin n) a E) (B : Matrix (Fin n) b E) :
    Aᵀ * J * B.map σ = (Formalism.UG.cT (σ : E →+* E) B * ((1 : E) • J.map σ) * A)ᵀ := by
  have : J.map σ = Jᵀ := by ext i j; simp [hJ]
  rw [this]
  simp only [Formalism.UG.cT, one_smul, Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.mul_assoc]
  rfl

end

theorem exists_perp_basis : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), (∀ i j, σ (J j i) = J i j) → J.det ≠ 0 →
    ∀ (r₀ : ℕ) (Xf Yf : Matrix (Fin n) (Fin r₀) E), GlobalTheory.SiegelSet.IsWittFrame σ ((1 : E) • J.map σ) Xf Yf →
    ∃ (n₀ : ℕ) (Z₀ : Matrix (Fin n) (Fin n₀) E) (Q : Matrix (Fin n₀ ⊕ (Fin r₀ ⊕ Fin r₀)) (Fin n) E),
      n₀ + (r₀ + r₀) = n ∧
      Q * Matrix.fromCols Z₀ (Matrix.fromCols Xf Yf) = 1 ∧ Matrix.fromCols Z₀ (Matrix.fromCols Xf Yf) * Q = 1 ∧
      (Matrix.fromCols Z₀ (Matrix.fromCols Xf Yf))ᵀ * J * (Matrix.fromCols Z₀ (Matrix.fromCols Xf Yf)).map σ =
        Matrix.fromBlocks (Z₀ᵀ * J * Z₀.map σ) 0 0 (Matrix.fromBlocks 0 1 1 0) ∧
      (Z₀ᵀ * J * Z₀.map σ).det ≠ 0 ∧ (∀ i j, σ ((Z₀ᵀ * J * Z₀.map σ) j i) = (Z₀ᵀ * J * Z₀.map σ) i j) ∧
      Formalism.UG.cT (σ : E →+* E) Xf * ((1 : E) • J.map σ) * Z₀ = 0 ∧ Formalism.UG.cT (σ : E →+* E) Yf * ((1 : E) • J.map σ) * Z₀ = 0 := by
  intro F E _ _ _ _ _ σ hcm n J hJ hdet r₀ X Y hW
  have hσ : ∀ x, σ (σ x) = x := GlobalTheory.SiegelSet.sigma_sigma hcm
  have gxx : Xᵀ * J * X.map σ = 0 := by rw [gram_eq_transpose σ J hJ, hW.xx]; simp
  have gyy : Yᵀ * J * Y.map σ = 0 := by rw [gram_eq_transpose σ J hJ, hW.yy]; simp
  have gyx : Yᵀ * J * X.map σ = 1 := by rw [gram_eq_transpose σ J hJ, hW.xy]; simp
  have gxy : Xᵀ * J * Y.map σ = 1 := by
    rw [gram_eq_map σ hσ J, hW.xy]; exact Matrix.map_one _ (map_zero σ) (map_one σ)
  have hyx : Formalism.UG.cT (σ : E →+* E) Y * ((1 : E) • J.map σ) * X = 1 := by
    have := gram_eq_transpose σ J hJ X Y
    rw [gxy] at this
    rw [← Matrix.transpose_transpose (_ * X), ← this, Matrix.transpose_one]
  have hGB : Matrix.fromRows (Formalism.UG.cT (σ : E →+* E) X * ((1 : E) • J.map σ))
      (Formalism.UG.cT (σ : E →+* E) Y * ((1 : E) • J.map σ)) * Matrix.fromCols X Y =
      Matrix.fromBlocks 0 1 1 0 := by
    rw [Matrix.fromRows_mul_fromCols, hW.xx, hW.yy, hW.xy, hyx]
  obtain ⟨n₀, Z, Q, hn, hQP, hPQ, hGZ⟩ := exists_ker_basis
    (Matrix.fromRows (Formalism.UG.cT (σ : E →+* E) X * ((1 : E) • J.map σ))
      (Formalism.UG.cT (σ : E →+* E) Y * ((1 : E) • J.map σ))) (Matrix.fromCols X Y)
    (by rw [hGB, Matrix.fromBlocks_multiply]; simp)
  rw [Matrix.fromRows_mul] at hGZ
  have hXZ : Formalism.UG.cT (σ : E →+* E) X * ((1 : E) • J.map σ) * Z = 0 := by
    ext i j; exact congrFun (congrFun hGZ (Sum.inl i)) j
  have hYZ : Formalism.UG.cT (σ : E →+* E) Y * ((1 : E) • J.map σ) * Z = 0 := by
    ext i j; exact congrFun (congrFun hGZ (Sum.inr i)) j
  have gzx : Zᵀ * J * X.map σ = 0 := by rw [gram_eq_transpose σ J hJ, hXZ]; simp
  have gzy : Zᵀ * J * Y.map σ = 0 := by rw [gram_eq_transpose σ J hJ, hYZ]; simp
  have gxz : Xᵀ * J * Z.map σ = 0 := by
    rw [gram_eq_map σ hσ J, hXZ]; exact Matrix.map_zero _ (map_zero σ)
  have gyz : Yᵀ * J * Z.map σ = 0 := by
    rw [gram_eq_map σ hσ J, hYZ]; exact Matrix.map_zero _ (map_zero σ)
  have hgram : (Matrix.fromCols Z (Matrix.fromCols X Y))ᵀ * J *
      (Matrix.fromCols Z (Matrix.fromCols X Y)).map σ =
      Matrix.fromBlocks (Zᵀ * J * Z.map σ) 0 0 (Matrix.fromBlocks 0 1 1 0) := by
    simp only [Matrix.transpose_fromCols, Matrix.fromCols_map]
    rw [Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols, Matrix.fromRows_mul,
      Matrix.fromRows_mul_fromCols, Matrix.mul_fromCols, Matrix.fromRows_mul,
      gxx, gyy, gyx, gxy, gzx, gzy, gxz, gyz]
    simp
  refine ⟨n₀, Z, Q, by simpa using hn, hQP, hPQ, hgram, ?_, ?_, hXZ, hYZ⟩
  · set P := Matrix.fromCols Z (Matrix.fromCols X Y) with hP
    have hJu : IsUnit J.det := hdet.isUnit
    have h1 : P.map σ * Q.map σ = 1 := by
      rw [← Matrix.map_mul, hPQ]; exact Matrix.map_one _ (map_zero σ) (map_one σ)
    have h2 : Pᵀ * Qᵀ = 1 := by rw [← Matrix.transpose_mul, hQP, Matrix.transpose_one]
    have h3 : (Pᵀ * J * P.map σ) * (Q.map σ * J⁻¹ * Qᵀ) = 1 := by
      calc _ = Pᵀ * (J * ((P.map σ * Q.map σ) * J⁻¹)) * Qᵀ := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [h1, Matrix.one_mul, Matrix.mul_nonsing_inv _ hJu, Matrix.mul_one, h2]
    have h4 := congrArg Matrix.det h3
    rw [Matrix.det_mul, hgram, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one] at h4
    intro h0
    rw [h0] at h4
    simp at h4
  · intro i j
    have h1 := congrFun (congrFun (gram_eq_map σ hσ J Z Z) j) i
    have h2 := congrFun (congrFun (gram_eq_transpose σ J hJ Z Z) i) j
    rw [h1, h2, Matrix.map_apply, hσ, Matrix.transpose_apply]

end GlobalTheory.SiegelSet.PerpBasis
end

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.witt_frame_extends_to_block_basis : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), (∀ i j, σ (J j i) = J i j) → J.det ≠ 0 →
    ∀ (r₀ : ℕ) (Xf Yf : Matrix (Fin n) (Fin r₀) E), GlobalTheory.SiegelSet.IsWittFrame σ ((1 : E) • J.map σ) Xf Yf →
    ∃ (n₀ : ℕ) (Z₀ : Matrix (Fin n) (Fin n₀) E) (Q : Matrix (Fin n₀ ⊕ (Fin r₀ ⊕ Fin r₀)) (Fin n) E),
      n₀ + (r₀ + r₀) = n ∧
      Q * Matrix.fromCols Z₀ (Matrix.fromCols Xf Yf) = 1 ∧ Matrix.fromCols Z₀ (Matrix.fromCols Xf Yf) * Q = 1 ∧
      (Matrix.fromCols Z₀ (Matrix.fromCols Xf Yf))ᵀ * J * (Matrix.fromCols Z₀ (Matrix.fromCols Xf Yf)).map σ =
        Matrix.fromBlocks (Z₀ᵀ * J * Z₀.map σ) 0 0 (Matrix.fromBlocks 0 1 1 0) ∧
      (Z₀ᵀ * J * Z₀.map σ).det ≠ 0 ∧ (∀ i j, σ ((Z₀ᵀ * J * Z₀.map σ) j i) = (Z₀ᵀ * J * Z₀.map σ) i j) ∧
      Formalism.UG.cT (σ : E →+* E) Xf * ((1 : E) • J.map σ) * Z₀ = 0 ∧ Formalism.UG.cT (σ : E →+* E) Yf * ((1 : E) • J.map σ) * Z₀ = 0 := by
  atlas_forward_decl GlobalTheory.SiegelSet.PerpBasis.exists_perp_basis
end

section
section
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

namespace GlobalTheory.WeilM

theorem symp_fromBlocks_hyperbolic :
    ∀ {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (c : S →ₐ[R] S) (ξ : S) {α β : Type} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] (r₀ : ℕ) (J₀ : Matrix α α S) (K : Matrix β β S)
    (z z' : Matrix (α ⊕ (Fin r₀ ⊕ Fin r₀)) β S),
    symp c ξ (Matrix.fromBlocks J₀ 0 0 (Matrix.fromBlocks 0 1 1 0)) K z z' =
      symp c ξ J₀ K (Matrix.of fun i l => z (Sum.inl i) l) (Matrix.of fun i l => z' (Sum.inl i) l) +
      ∑ i, (Algebra.trace R S (ξ * ∑ j, ∑ l, z (Sum.inr (Sum.inl i)) j * K j l * c (z' (Sum.inr (Sum.inr i)) l)) +
        Algebra.trace R S (ξ * ∑ j, ∑ l, z (Sum.inr (Sum.inr i)) j * K j l * c (z' (Sum.inr (Sum.inl i)) l))) := by
  intro R S _ _ _ c ξ α β _ _ _ _ r₀ J₀ K z z'
  simp only [symp, hTens, ← map_add, ← map_sum, ← mul_add, ← Finset.mul_sum]
  congr 2
  simp only [Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.of_apply,
    mul_zero, zero_mul, Finset.sum_const_zero, add_zero, zero_add, Finset.sum_add_distrib]
  congr 1
  rw [add_comm]
  congr 1 <;>
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp [Matrix.one_apply]

end GlobalTheory.WeilM
end

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplectic_pairing_block_reduction : ∀ {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (c : S →ₐ[R] S) (ξ : S) {α β : Type} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] (r₀ : ℕ) (J₀ : Matrix α α S) (K : Matrix β β S)
    (z z' : Matrix (α ⊕ (Fin r₀ ⊕ Fin r₀)) β S),
    symp c ξ (Matrix.fromBlocks J₀ 0 0 (Matrix.fromBlocks 0 1 1 0)) K z z' =
      symp c ξ J₀ K (Matrix.of fun i l => z (Sum.inl i) l) (Matrix.of fun i l => z' (Sum.inl i) l) +
      ∑ i, (Algebra.trace R S (ξ * ∑ j, ∑ l, z (Sum.inr (Sum.inl i)) j * K j l * c (z' (Sum.inr (Sum.inr i)) l)) +
        Algebra.trace R S (ξ * ∑ j, ∑ l, z (Sum.inr (Sum.inr i)) j * K j l * c (z' (Sum.inr (Sum.inl i)) l))) := by
  atlas_forward_decl GlobalTheory.WeilM.symp_fromBlocks_hyperbolic
end

section
section
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical
noncomputable section

namespace GlobalTheory.TorusAdapted

section Coords

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {n₀ r₀ d : ℕ}

def top (u : Matrix (Fin n₀ ⊕ (Fin r₀ ⊕ Fin r₀)) (Fin d) A) : Matrix (Fin n₀) (Fin d) A :=
  Matrix.of fun i l => u (Sum.inl i) l

def blockCo (e₀ : Matrix (Fin n₀) (Fin d) A ≃ₗ[R] (Fin n₀ × Fin d → R) × (Fin n₀ × Fin d → R))
    (p q : (Fin d → A) ≃ₗ[R] (Fin 2 × Fin d → R)) :
    Matrix (Fin n₀ ⊕ (Fin r₀ ⊕ Fin r₀)) (Fin d) A ≃ₗ[R]
      ((Fin n₀ × Fin d) ⊕ (Fin r₀ × (Fin 2 × Fin d)) → R) × ((Fin n₀ × Fin d) ⊕ (Fin r₀ × (Fin 2 × Fin d)) → R) where
  toFun u := (Sum.elim (e₀ (top u)).1 (fun k => q (u (Sum.inr (Sum.inr k.1))) k.2),
    Sum.elim (e₀ (top u)).2 (fun k => p (u (Sum.inr (Sum.inl k.1))) k.2))
  invFun fg := Matrix.of fun r l => Sum.elim (fun i => e₀.symm (fg.1 ∘ Sum.inl, fg.2 ∘ Sum.inl) i l)
    (Sum.elim (fun i => p.symm (fun k => fg.2 (Sum.inr (i, k))) l) (fun i => q.symm (fun k => fg.1 (Sum.inr (i, k))) l)) r
  map_add' u u' := by
    have ht : top (u + u') = top u + top u' := rfl
    have hr : ∀ r, (u + u') r = u r + u' r := fun _ => rfl
    rw [ht]
    ext (k | k) <;> simp [hr]
  map_smul' a u := by
    have ht : top (a • u) = a • top u := rfl
    have hr : ∀ r, (a • u) r = a • u r := fun _ => rfl
    rw [ht]
    ext (k | k) <;> simp [hr]
  left_inv u := by
    ext (i | i | i) l
    · simp only [Matrix.of_apply, Sum.elim_inl, Sum.elim_comp_inl]
      rw [show ((e₀ (top u)).1, (e₀ (top u)).2) = e₀ (top u) from rfl, LinearEquiv.symm_apply_apply]
      rfl
    · simp
    · simp
  right_inv fg := by
    rcases fg with ⟨f, g⟩
    set U : Matrix (Fin n₀ ⊕ (Fin r₀ ⊕ Fin r₀)) (Fin d) A := Matrix.of fun r l => Sum.elim
      (fun i => e₀.symm (f ∘ Sum.inl, g ∘ Sum.inl) i l) (Sum.elim (fun i => p.symm (fun k => g (Sum.inr (i, k))) l)
        (fun i => q.symm (fun k => f (Sum.inr (i, k))) l)) r with hU
    have ht : top U = e₀.symm (f ∘ Sum.inl, g ∘ Sum.inl) := by ext i l; simp [top, hU]
    have hx : ∀ i, U (Sum.inr (Sum.inl i)) = p.symm (fun k => g (Sum.inr (i, k))) := fun i => by funext l; simp [hU]
    have hy : ∀ i, U (Sum.inr (Sum.inr i)) = q.symm (fun k => f (Sum.inr (i, k))) := fun i => by funext l; simp [hU]
    show (Sum.elim (e₀ (top U)).1 (fun k => q (U (Sum.inr (Sum.inr k.1))) k.2),
      Sum.elim (e₀ (top U)).2 (fun k => p (U (Sum.inr (Sum.inl k.1))) k.2)) = (f, g)
    simp only [ht, hx, hy, LinearEquiv.apply_symm_apply]
    ext (k | ⟨i, k⟩) <;> simp

theorem blockCo_apply (e₀ : Matrix (Fin n₀) (Fin d) A ≃ₗ[R] (Fin n₀ × Fin d → R) × (Fin n₀ × Fin d → R))
    (p q : (Fin d → A) ≃ₗ[R] (Fin 2 × Fin d → R)) (u : Matrix (Fin n₀ ⊕ (Fin r₀ ⊕ Fin r₀)) (Fin d) A) :
    blockCo e₀ p q u = (Sum.elim (e₀ (top u)).1 (fun k => q (u (Sum.inr (Sum.inr k.1))) k.2),
      Sum.elim (e₀ (top u)).2 (fun k => p (u (Sum.inr (Sum.inl k.1))) k.2)) := rfl

def mulLeftE {m m' : Type} [Fintype m] [Fintype m'] [DecidableEq m] [DecidableEq m'] (Q : Matrix m' m A)
    (P : Matrix m m' A) (h1 : P * Q = 1) (h2 : Q * P = 1) : Matrix m (Fin d) A ≃ₗ[R] Matrix m' (Fin d) A where
  toFun w := Q * w
  invFun z := P * z
  map_add' := Matrix.mul_add Q
  map_smul' a w := Matrix.mul_smul Q a w
  left_inv w := by
    show P * (Q * w) = w
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  right_inv z := by
    show Q * (P * z) = z
    rw [← Matrix.mul_assoc, h2, Matrix.one_mul]

end Coords

theorem infScale_one (F : Type) [Field F] [NumberField F] : GlobalTheory.TorusTheta.infScale F 1 = 1 := by
  unfold GlobalTheory.TorusTheta.infScale
  rw [map_one, map_one]
  rfl

end GlobalTheory.TorusAdapted

namespace GlobalTheory.TorusAdapted

theorem adapted_torus : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ (r₀ : ℕ) (Xf Yf : Matrix (Fin n) (Fin r₀) E),
    GlobalTheory.SiegelSet.IsWittFrame σ ((1 : E) • X.J.map σ) Xf Yf →
    ∃ (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)) (Fin n × Fin d))
      (blk : Fin n × Fin d → Option (Fin r₀)),
      (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
        co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) ∧
      (∀ i : Fin r₀, (Finset.univ.filter (fun j => blk j = some i)).card = 2 * d) ∧
      ∀ t : Fin r₀ → ℝ, (∀ i, 0 < t i) → ∀ a, GlobalTheory.SiegelSet.IsTorusElt σ ((1 : E) • X.J.map σ) Xf Yf t a →
        ∀ a' : UA σ X.J, (a' : GL (Fin n) (AE F E)) = HA.mat (AF F) σ ((1 : E) • X.J.map σ) a →
        ∀ z : Matrix (Fin n) (Fin d) (AE F E), co.e (mat a' * z) =
          (fun j => GlobalTheory.TorusTheta.infScale F (((blk j).elim 1 t)⁻¹) * (co.e z).1 j,
           fun j => GlobalTheory.TorusTheta.infScale F ((blk j).elim 1 t) * (co.e z).2 j) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP r₀ Xf Yf hWF
  have hB := hP.base
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hσ : ∀ x, σ (σ x) = x := fun x => by
    apply ((B.emb w).1 : E →+* ℂ).injective
    rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star]
  have hX' : X.J.det ≠ 0 := fun h0 => by
    apply GlobalTheory.RatDarboux.det_ne_zero_of_isCartan (hP.herm.cartan w)
    have := ((B.emb w).1 : E →+* ℂ).map_det X.J
    rw [h0, map_zero] at this
    exact this.symm
  have hW' : W.J.det ≠ 0 := fun h0 => by
    apply GlobalTheory.RatDarboux.det_ne_zero_of_isCartan (hP.skew.cartan w)
    have := ((B.emb w).1 : E →+* ℂ).map_det W.J
    rw [h0, map_zero] at this
    rw [Matrix.det_smul]
    exact mul_eq_zero_of_right _ this.symm
  have h2 : Module.finrank F E = 2 := hB.cm.2.2.1
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h2
  obtain ⟨n₀, Z₀, Q, hn, hQP, hPQ, hG, hJ₀, hJ₀h, hZx, hZy⟩ := GlobalTheory.T.witt_frame_extends_to_block_basis F E σ hB.cm n X.J hP.herm.herm hX' r₀ Xf Yf hWF
  set P := Matrix.fromCols Z₀ (Matrix.fromCols Xf Yf) with hPdef
  obtain ⟨co₀, hco₀⟩ := GlobalTheory.RatDarboux.exists_darboux (AF F) h2 σ hσ hJ₀h hP.skew.skew hJ₀ hW'
  obtain ⟨p, q, hpq, hpq', hpr, hqr⟩ := GlobalTheory.T.quadratic_extension_symplectic_coordinates σ d W.J hσ h2 hP.skew.skew hW'
  have hinc : ∀ {a b c : Type} [Fintype b] (U : Matrix a b E) (V : Matrix b c E),
      incM F (U * V) = incM F U * incM F V := fun U V => Matrix.map_mul
  have h1 : incM F P * incM F Q = 1 := by
    rw [← hinc, hPQ]; exact Matrix.map_one _ (map_zero _) (map_one _)
  have h1' : incM F Q * incM F P = 1 := by
    rw [← hinc, hQP]; exact Matrix.map_one _ (map_zero _) (map_one _)
  let eb := blockCo (R := AF F) (r₀ := r₀) co₀.e p q
  let mQ : Matrix (Fin n) (Fin d) (AE F E) ≃ₗ[AF F] Matrix (Fin n₀ ⊕ (Fin r₀ ⊕ Fin r₀)) (Fin d) (AE F E) :=
    mulLeftE (incM F Q) (incM F P) h1 h1'
  have hcard : Fintype.card ((Fin n₀ × Fin d) ⊕ (Fin r₀ × (Fin 2 × Fin d))) = Fintype.card (Fin n × Fin d) := by
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    rw [← hn]; ring
  let ε := Fintype.equivOfCardEq hcard
  let e := mQ.trans (eb.trans (LinearEquiv.prodCongr (LinearEquiv.funCongrLeft (AF F) (AF F) ε.symm)
    (LinearEquiv.funCongrLeft (AF F) (AF F) ε.symm)))
  have he : ∀ z, e z = ((eb (incM F Q * z)).1 ∘ ε.symm, (eb (incM F Q * z)).2 ∘ ε.symm) := fun z => rfl

  have hGinc : (incM F P)ᵀ * incM F X.J * (incM F P).map (cA σ) =
      Matrix.fromBlocks (incM F (Z₀ᵀ * X.J * Z₀.map σ)) 0 0 (Matrix.fromBlocks 0 1 1 0) := by
    rw [show (incM F P)ᵀ * incM F X.J * (incM F P).map (cA σ) = incM F (Pᵀ * X.J * P.map σ) by rw [hinc, hinc]; rfl, hG]
    simp [incM, Matrix.fromBlocks_map]
  have hform₀ : ∀ x y, symp (R := AF F) (cA σ) (-1) (incM F (Z₀ᵀ * X.J * Z₀.map σ)) (incM F W.J) x y =
      (co₀.e x).1 ⬝ᵥ (co₀.e y).2 - (co₀.e y).1 ⬝ᵥ (co₀.e x).2 := co₀.form
  have hdot : ∀ f g : (Fin n₀ × Fin d) ⊕ (Fin r₀ × (Fin 2 × Fin d)) → AF F, (f ∘ ε.symm) ⬝ᵥ (g ∘ ε.symm) = f ⬝ᵥ g :=
    fun f g => by
      simp only [dotProduct, Function.comp]
      exact Equiv.sum_comp ε.symm (fun k => f k * g k)
  have hform : ∀ w₁ w₂, symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) w₁ w₂ =
      (e w₁).1 ⬝ᵥ (e w₂).2 - (e w₂).1 ⬝ᵥ (e w₁).2 := by
    intro w₁ w₂
    have e1 : symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) w₁ w₂ =
        symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) (incM F P * (incM F Q * w₁)) (incM F P * (incM F Q * w₂)) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.one_mul]
    have key : ∀ i, Algebra.trace (AF F) (AE F E) (-1 * ∑ j, ∑ l, (incM F Q * w₁) (Sum.inr (Sum.inl i)) j *
          incM F W.J j l * cA σ ((incM F Q * w₂) (Sum.inr (Sum.inr i)) l)) +
        Algebra.trace (AF F) (AE F E) (-1 * ∑ j, ∑ l, (incM F Q * w₁) (Sum.inr (Sum.inr i)) j *
          incM F W.J j l * cA σ ((incM F Q * w₂) (Sum.inr (Sum.inl i)) l)) =
        q ((incM F Q * w₁) (Sum.inr (Sum.inr i))) ⬝ᵥ p ((incM F Q * w₂) (Sum.inr (Sum.inl i))) -
          q ((incM F Q * w₂) (Sum.inr (Sum.inr i))) ⬝ᵥ p ((incM F Q * w₁) (Sum.inr (Sum.inl i))) := fun i => by
      rw [neg_one_mul, neg_one_mul, map_neg, ← hpq', ← hpq]; ring
    rw [e1, GlobalTheory.T.symplectic_form_base_change_matrix, hGinc, GlobalTheory.T.symplectic_pairing_block_reduction, hform₀, he, he, hdot, hdot, blockCo_apply, blockCo_apply]
    simp only [key, sumElim_dotProduct_sumElim, top]
    simp only [dotProduct, Fintype.sum_prod_type, Finset.sum_sub_distrib]
    ring

  refine ⟨⟨e, hform⟩, fun j => Sum.elim (fun _ => (none : Option (Fin r₀))) (fun k => some k.1) (ε.symm j), ?_, ?_, ?_⟩
  · intro x
    obtain ⟨y₀, z₀, h₀⟩ := hco₀ (top (Q * x))
    choose yq hyq using fun i => hqr ((Q * x) (Sum.inr (Sum.inr i)))
    choose yp hyp using fun i => hpr ((Q * x) (Sum.inr (Sum.inl i)))
    refine ⟨Sum.elim y₀ (fun k => yq k.1 k.2) ∘ ε.symm, Sum.elim z₀ (fun k => yp k.1 k.2) ∘ ε.symm, ?_⟩
    have ht : top (incM F (Q * x)) = (top (Q * x)).map (inclR (F := F) (AF F)) := rfl
    have hr : ∀ r, incM F (Q * x) r = incV F ((Q * x) r) := fun _ => rfl
    rw [he, ← hinc, blockCo_apply, ht, h₀]
    simp only [hr, hyq, hyp]
    refine Prod.ext (funext fun j => ?_) (funext fun j => ?_) <;> simp only [Function.comp_apply] <;>
      generalize ε.symm j = k' <;> rcases k' with k | ⟨i, k⟩ <;> simp
  · intro i
    rw [Finset.card_filter, ← Equiv.sum_comp ε]
    simp only [Equiv.symm_apply_apply, Fintype.sum_sum_type, Fintype.sum_prod_type, Sum.elim_inl, Sum.elim_inr,
      Option.some.injEq, reduceCtorEq, if_false, Finset.sum_const_zero, zero_add]
    rw [Finset.sum_eq_single i (fun b _ hb => by simp [hb]) (by simp)]
    simp
  · intro t ht a hT a' ha' z
    have hm : mat a' = ((HA.mat (AF F) σ ((1 : E) • X.J.map σ) a : GL (Fin n) (AE F E)) :
        Matrix (Fin n) (Fin n) (AE F E)) := by
      rw [show mat a' = ((a' : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) from rfl, ha']
    obtain ⟨hx, hy, h0⟩ := GlobalTheory.T.torus_element_acts_on_frame_columns F E σ hB.cm n ((1 : E) • X.J.map σ) r₀ Xf Yf t ht a hT
    generalize ((HA.mat (AF F) σ ((1 : E) • X.J.map σ) a : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) = m
      at hx hy h0 hm
    have hc : ∀ C : Matrix (Fin n) (Fin r₀) E, Formalism.UG.cT (σ : E →+* E) C * ((1 : E) • X.J.map σ) * Z₀ = 0 → ∀ c,
        (Formalism.UG.cT (σ : E →+* E) C * ((1 : E) • X.J.map σ)) *ᵥ (fun k => Z₀ k c) = 0 := fun C hC c => by
      funext i; exact congrFun (congrFun hC i) c
    have hZ : m * incM F Z₀ = incM F Z₀ := by
      ext r c
      exact congrFun (h0 (fun k => Z₀ k c) (hc Xf hZx c) (hc Yf hZy c)) r
    have hPc : incM F P = Matrix.fromCols (incM F Z₀) (Matrix.fromCols (incM F Xf) (incM F Yf)) := by
      ext r (c | c | c) <;> rfl
    set Dm : Matrix (Fin n₀ ⊕ (Fin r₀ ⊕ Fin r₀)) (Fin n₀ ⊕ (Fin r₀ ⊕ Fin r₀)) (AE F E) := Matrix.fromBlocks 1 0 0
      (Matrix.fromBlocks (Matrix.diagonal fun i => algebraMap (AF F) (AE F E) (GlobalTheory.TorusTheta.infScale F (t i))) 0 0
        (Matrix.diagonal fun i => algebraMap (AF F) (AE F E) (GlobalTheory.TorusTheta.infScale F (t i)⁻¹))) with hDm
    have hMP : m * incM F P = incM F P * Dm := by
      rw [hPc, Matrix.mul_fromCols, Matrix.mul_fromCols, hZ, hx, hy, hDm, Matrix.fromCols_mul_fromBlocks,
        Matrix.fromCols_mul_fromBlocks]
      simp
    have hQm : incM F Q * (m * z) = Dm * (incM F Q * z) := by
      calc incM F Q * (m * z) = incM F Q * (m * (incM F P * (incM F Q * z))) := by
            rw [← Matrix.mul_assoc (incM F P), h1, Matrix.one_mul]
        _ = incM F Q * (m * incM F P) * (incM F Q * z) := by simp only [Matrix.mul_assoc]
        _ = Dm * (incM F Q * z) := by rw [hMP, ← Matrix.mul_assoc (incM F Q) (incM F P) Dm, h1', Matrix.one_mul]
    have hD1 : ∀ u : Matrix (Fin n₀ ⊕ (Fin r₀ ⊕ Fin r₀)) (Fin d) (AE F E), top (Dm * u) = top u := fun u => by
      ext i l; simp [top, hDm, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
    have hD2 : ∀ (u : Matrix (Fin n₀ ⊕ (Fin r₀ ⊕ Fin r₀)) (Fin d) (AE F E)) i,
        (Dm * u) (Sum.inr (Sum.inl i)) = GlobalTheory.TorusTheta.infScale F (t i) • u (Sum.inr (Sum.inl i)) := fun u i => by
      funext l; simp [hDm, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.diagonal_apply, Algebra.smul_def]
    have hD3 : ∀ (u : Matrix (Fin n₀ ⊕ (Fin r₀ ⊕ Fin r₀)) (Fin d) (AE F E)) i,
        (Dm * u) (Sum.inr (Sum.inr i)) = GlobalTheory.TorusTheta.infScale F (t i)⁻¹ • u (Sum.inr (Sum.inr i)) := fun u i => by
      funext l; simp [hDm, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.diagonal_apply, Algebra.smul_def]
    rw [hm, he, he, hQm, blockCo_apply, blockCo_apply, hD1]
    simp only [hD2, hD3, map_smul]
    refine Prod.ext (funext fun j => ?_) (funext fun j => ?_) <;> simp only [Function.comp_apply] <;>
      generalize ε.symm j = k' <;> rcases k' with k | ⟨i, k⟩ <;> simp [infScale_one]

end GlobalTheory.TorusAdapted
end
end

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.witt_frame_darboux_coordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ (r₀ : ℕ) (Xf Yf : Matrix (Fin n) (Fin r₀) E),
    GlobalTheory.SiegelSet.IsWittFrame σ ((1 : E) • X.J.map σ) Xf Yf →
    ∃ (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)) (Fin n × Fin d))
      (blk : Fin n × Fin d → Option (Fin r₀)),
      (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
        co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) ∧
      (∀ i : Fin r₀, (Finset.univ.filter (fun j => blk j = some i)).card = 2 * d) ∧
      ∀ t : Fin r₀ → ℝ, (∀ i, 0 < t i) → ∀ a, GlobalTheory.SiegelSet.IsTorusElt σ ((1 : E) • X.J.map σ) Xf Yf t a →
        ∀ a' : UA σ X.J, (a' : GL (Fin n) (AE F E)) = HA.mat (AF F) σ ((1 : E) • X.J.map σ) a →
        ∀ z : Matrix (Fin n) (Fin d) (AE F E), co.e (mat a' * z) =
          (fun j => GlobalTheory.TorusTheta.infScale F (((blk j).elim 1 t)⁻¹) * (co.e z).1 j,
           fun j => GlobalTheory.TorusTheta.infScale F ((blk j).elim 1 t) * (co.e z).2 j) := by
  atlas_forward_decl GlobalTheory.TorusAdapted.adapted_torus
end

section
section
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

noncomputable section

namespace GlobalTheory.ModelChangeTo

theorem change_to_coordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)) (Fin n × Fin d),
    (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
        co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
    ∃ (M₁ : Model σ X W) (om₁ : Rep σ X W) (e : Fn F n d →ₗ[ℂ] Fn F n d) (c₀ : ℂ),
      M₁.co = co ∧ IsPair B M₁ χX χW om₁ r s r' s' ∧ c₀ ≠ 0 ∧
      ∀ Φ ∈ schA F (Fin n × Fin d), e Φ ∈ schA F (Fin n × Fin d) ∧ thetaSum F (e Φ) = c₀ * thetaSum F Φ ∧
        ∀ x, e (om x Φ) = om₁ x (e Φ) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hpair co hco
  obtain ⟨e, ei, ev, hei, hmaps, hheis, hSB, hvac, hstd, hpure, hbij⟩ :=
    GlobalTheory.T.darboux_coords_good_model F E σ B n d X W M r s r' s' hpair.base hpair.herm hpair.skew hpair.good co hco
  let M₁ : Model σ X W := ⟨co, fun v => ev v (M.vac v), M.μ, M.dom⟩
  have hM₁ : M₁.IsGood B.ψ := ⟨hco, hvac, hstd, hpair.good.haar, hpair.good.dom⟩
  have hne : ∃ f : SInf F (Fin n × Fin d), f ≠ 0 := by
    by_contra hall
    push_neg at hall
    obtain ⟨φ, hφ, hθ⟩ := GlobalTheory.ThetaSumNe.exists_mem_schA_thetaSum_ne_zero F (Fin n × Fin d)
    have hle : schA F (Fin n × Fin d) ≤ ⊥ := by
      refine Submodule.span_le.2 ?_
      rintro Φ ⟨f, g, -, rfl⟩
      rw [hall f]
      show pureA F 0 g = 0
      funext x
      simp [pureA]
    have h0 : φ = 0 := (Submodule.mem_bot ℂ).1 (hle hφ)
    exact hθ (by rw [h0]; simp [thetaSum])
  have hev : IsEv B M M₁ 1 1 ∅ e := by
    refine ⟨hmaps, fun z Φ hΦ => ?_, fun u hu => hu.elim, ei, ev, ?_, fun v => ⟨rfl, hSB v⟩, hpure⟩
    · have h1 : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
      have h1' : incM F (1 : Matrix (Fin d) (Fin d) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
      rw [h1, h1', Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one]
      exact hheis z Φ hΦ
    · obtain ⟨f, hf⟩ := hne
      obtain ⟨g, rfl⟩ := hei f
      intro h
      exact hf (by rw [h]; rfl)
  obtain ⟨om₁, hW, hint⟩ := GlobalTheory.T.weil_eigen_bijective_schwartz F E σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e hev hbij
  obtain ⟨c₀, hc₀, hth⟩ := GlobalTheory.T.weil_eigen_schwartz_surjective F E σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e hev hbij
  exact ⟨M₁, om₁, e, c₀, rfl, ⟨hpair.base, hpair.herm, hpair.skew, hM₁, hpair.hX, hpair.hW, hpair.resX, hpair.resW, hW⟩,
    hc₀, fun Φ hΦ => ⟨hmaps Φ hΦ, hth Φ hΦ, fun x => hint x Φ hΦ⟩⟩

end GlobalTheory.ModelChangeTo

end
end

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.darboux_coords_rational_points : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)) (Fin n × Fin d),
    (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
        co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
    ∃ (M₁ : Model σ X W) (om₁ : Rep σ X W) (e : Fn F n d →ₗ[ℂ] Fn F n d) (c₀ : ℂ),
      M₁.co = co ∧ IsPair B M₁ χX χW om₁ r s r' s' ∧ c₀ ≠ 0 ∧
      ∀ Φ ∈ schA F (Fin n × Fin d), e Φ ∈ schA F (Fin n × Fin d) ∧ thetaSum F (e Φ) = c₀ * thetaSum F Φ ∧
        ∀ x, e (om x Φ) = om₁ x (e Φ) := by
  atlas_forward_decl GlobalTheory.ModelChangeTo.change_to_coordinates
end

section
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_action_model_coordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (g : UA σ X.J) (u : Fin n × Fin d → ℝ), (∀ j, 0 < u j) →
    (∀ z : Matrix (Fin n) (Fin d) (AE F E), M.co.e (mat g * z) =
      (fun j => GlobalTheory.TorusTheta.infScale F ((u j)⁻¹) * (M.co.e z).1 j,
       fun j => GlobalTheory.TorusTheta.infScale F (u j) * (M.co.e z).2 j)) →
    ∃ κ : ℂ, ‖κ‖ ^ 2 = ∏ j, u j ^ Module.finrank ℚ F ∧
      ∀ Φ ∈ schA F (Fin n × Fin d), ∀ x, om (g, 1) Φ x = κ * Φ (fun j => GlobalTheory.TorusTheta.infScale F (u j) * x j) := by
  first | exact @GlobalTheory.TorusDilate.main | exact GlobalTheory.TorusDilate.main | (intros; apply GlobalTheory.TorusDilate.main <;> assumption)
end

section
section
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

noncomputable section

namespace GlobalTheory.FinDenom

theorem finDiv_finPart_mul' {F : Type} [Field F] [NumberField F] {N m : ℕ} {T : AF F} (hT : GlobalTheory.FinSupp.FinDiv F N ((m : AF F) * T))
    (a : 𝓞 F) : GlobalTheory.FinSupp.FinDiv F N (GlobalTheory.FinSupp.finPart F (algebraMap F (AF F) ((m : F) * (a : F))) * T) := by
  intro v
  obtain ⟨b, hb, e⟩ := hT v
  have ha : algebraMap F (Fv F v) (a : F) ∈ v.adicCompletionIntegers F := HeightOneSpectrum.coe_mem_adicCompletionIntegers v a
  refine ⟨algebraMap F (Fv F v) (a : F) * b, mul_mem ha hb, ?_⟩
  have e1 : evFin F v (GlobalTheory.FinSupp.finPart F (algebraMap F (AF F) ((m : F) * (a : F)))) =
      evFin F v (algebraMap F (AF F) ((m : F) * (a : F))) := rfl
  rw [map_mul, e1, AlgHom.commutes, map_mul, map_natCast]
  simp only [map_mul, map_natCast] at e
  rw [mul_comm ((m : Fv F v)) _, mul_assoc, e]
  ring

theorem finPart_mul_congr {F : Type} [Field F] [NumberField F] (x : AF F) {y z : AF F} (h : y.2 = z.2) :
    GlobalTheory.FinSupp.finPart F x * y = GlobalTheory.FinSupp.finPart F (x * z) :=
  Prod.ext (zero_mul _) (by show x.2 * y.2 = x.2 * z.2; rw [h])

theorem exists_denominator_of_finite_component : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ Φ ∈ schA F (Fin n × Fin d), ∃ (C : ℝ) (k : ℕ), ∀ g h, ∃ m : ℕ, 1 ≤ m ∧ (m : ℝ) ≤ C * ((ht g : ℝ) * ht h) ^ k ∧
      ∀ (x : Fin n × Fin d → AF F) (ξ : Fin n × Fin d → F), (∀ i, (x i).2 = (algebraMap F (AF F) (ξ i)).2) →
        om (g, h) Φ x ≠ 0 → ∀ i, IsIntegral ℤ ((m : F) * ξ i) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP Φ hΦ
  have S := hP.weil.isUSplitting
  have hstd : IsStd B.ψ := hP.base.std
  obtain ⟨N, hN1, hinv⟩ := GlobalTheory.T.adelicSchwartz_fixed_by_small_heisenberg_lattice F (Fin n × Fin d) B.ψ hstd.1 Φ hΦ
  obtain ⟨C, k, hC⟩ := GlobalTheory.T.exists_scale_movedHeisenbergLattice_polynomial_heights F E n d (Fin n × Fin d) M.co.e N hN1
  obtain ⟨D, hD1, hD⟩ := GlobalTheory.T.exists_bounded_denominator_standardChar_trivial F
  refine ⟨D * C, k, fun g h => ?_⟩
  obtain ⟨m, hm1, hmC, hmT⟩ := hC g.1 h.1
  refine ⟨D * m, Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), ?_, ?_⟩
  · push_cast
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hmC (by positivity)
  · intro x ξ hxξ hξ i
    have key : ∀ a : 𝓞 F, B.ψ (GlobalTheory.FinSupp.finPart F (algebraMap F (AF F) ((a : F) * ((m : F) * ξ i)))) = 1 := by
      intro a
      set c : AF F := GlobalTheory.FinSupp.finPart F (algebraMap F (AF F) ((m : F) * (a : F))) with hc
      set y : Fin n × Fin d → AF F := c • Pi.single i 1 with hy
      set w' := M.co.e.symm (0, y) with hw'
      set p : UA σ X.J × UA σ W.J := (g, h) with hp
      set w := actAB (cA σ) p⁻¹ w' with hw
      have hwe : M.co.e w = c • M.co.e ((((g.1)⁻¹ : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) *
          M.co.e.symm (0, Pi.single i 1) * (((h.1⁻¹ : GL (Fin d) (AF F ⊗[F] E)) : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)))ᵀ) := by
        rw [hw, hw', hy, hp]
        rw [show ((0 : Fin n × Fin d → AF F), c • Pi.single i (1 : AF F)) = c • ((0 : Fin n × Fin d → AF F), Pi.single i (1 : AF F)) by simp]
        rw [LinearEquiv.map_smul, ← LinearEquiv.map_smul M.co.e]
        congr 1
        simp only [actAB, Prod.inv_mk, Subgroup.coe_inv]
        rw [Matrix.mul_smul, Matrix.smul_mul]
      have hrho : M.co.rho B.ψ w Φ = Φ := by
        unfold Darboux.rho
        apply hinv
        intro l
        rw [hwe]
        obtain ⟨h1, h2⟩ := hmT i l
        refine ⟨?_, ?_, ?_, ?_⟩
        · show (c * _).1 = 0
          exact zero_mul _
        · rw [Prod.smul_fst, Pi.smul_apply, smul_eq_mul]
          exact finDiv_finPart_mul' h1 a
        · show (c * _).1 = 0
          exact zero_mul _
        · rw [Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
          exact finDiv_finPart_mul' h2 a
      have himpl := S.impl p w Φ hΦ
      rw [hrho] at himpl
      have hact : actAB (cA σ) p w = w' := by
        rw [hw]
        simp only [actAB, Prod.fst_inv, Prod.snd_inv, Subgroup.coe_inv, hp]
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul,
          Matrix.mul_assoc, ← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one,
          Matrix.mul_one]
      rw [hact] at himpl
      have hx := congrFun himpl x
      simp only [Darboux.rho, hw', LinearEquiv.apply_symm_apply, schr, zero_dotProduct, mul_zero, add_zero] at hx
      have h1 : B.ψ (x ⬝ᵥ y) = 1 := by
        have hne : om p Φ x ≠ 0 := hξ
        exact (mul_eq_right₀ hne).1 hx.symm
      rw [hy, dotProduct_smul, dotProduct_single, smul_eq_mul, mul_one, hc, finPart_mul_congr _ (hxξ i), ← map_mul] at h1
      convert h1 using 3
      ring_nf
    have := hD B.ψ hstd _ key
    convert this using 1
    push_cast
    ring

end GlobalTheory.FinDenom
end
end

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_theta_polynomial_growth : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ Φ ∈ schA F (Fin n × Fin d), ∃ (C : ℝ) (k : ℕ), ∀ g h, ∃ m : ℕ, 1 ≤ m ∧ (m : ℝ) ≤ C * ((ht g : ℝ) * ht h) ^ k ∧
      ∀ (x : Fin n × Fin d → AF F) (ξ : Fin n × Fin d → F), (∀ i, (x i).2 = (algebraMap F (AF F) (ξ i)).2) →
        om (g, h) Φ x ≠ 0 → ∀ i, IsIntegral ℤ ((m : F) * ξ i) := by
  atlas_forward_decl GlobalTheory.FinDenom.exists_denominator_of_finite_component
end

section
section
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

namespace GlobalTheory.TorusTheta

theorem min_pow_le_of_mem_cone {r : ℕ} {c : ℝ} (hc : 0 < c) {t : Fin r → ℝ}
    (ht : t ∈ GlobalTheory.SiegelSet.cone r c) (i : Fin r) : min 1 c ^ r ≤ t i := by
  obtain ⟨hpos, hstep, hlast⟩ := ht
  have hm0 : 0 < min 1 c := lt_min one_pos hc
  have hm1 : min 1 c ≤ 1 := min_le_left _ _
  have key : ∀ k : ℕ, ∀ i : Fin r, i.val + k + 1 = r → min 1 c ^ (k + 1) ≤ t i := by
    intro k
    induction k with
    | zero =>
      intro i hi
      simp only [zero_add, pow_one]
      exact (min_le_right _ _).trans (hlast i (by omega))
    | succ k ih =>
      intro i hi
      have hj : i.val + 1 < r := by omega
      have h1 := ih ⟨i.val + 1, hj⟩ (by simp; omega)
      have h2 := hstep i ⟨i.val + 1, hj⟩ rfl
      have h3 : 0 < t ⟨i.val + 1, hj⟩ := hpos _
      calc min 1 c ^ (k + 1 + 1) = min 1 c * min 1 c ^ (k + 1) := by ring
        _ ≤ min 1 c * t ⟨i.val + 1, hj⟩ := mul_le_mul_of_nonneg_left h1 hm0.le
        _ ≤ c * t ⟨i.val + 1, hj⟩ := mul_le_mul_of_nonneg_right (min_le_right _ _) h3.le
        _ ≤ t i := h2
  have := key (r - i.val - 1) i (by omega)
  refine le_trans ?_ this
  exact pow_le_pow_of_le_one hm0.le hm1 (by omega)

theorem mul_norm_le_norm_smul {ι V : Type} [Fintype ι] [NormedAddCommGroup V] [NormedSpace ℝ V] {c' : ℝ} (hc' : 0 < c')
    (s : ι → ℝ) (hs : ∀ i, c' ≤ s i) (v : ι → V) : c' * ‖v‖ ≤ ‖fun i => s i • v i‖ := by
  rw [← le_div_iff₀' hc']
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  rw [le_div_iff₀' hc']
  have hsi : 0 < s i := hc'.trans_le (hs i)
  calc c' * ‖v i‖ ≤ s i * ‖v i‖ := mul_le_mul_of_nonneg_right (hs i) (norm_nonneg _)
    _ = ‖s i • v i‖ := by rw [norm_smul, Real.norm_of_nonneg hsi.le]
    _ ≤ ‖fun i => s i • v i‖ := norm_le_pi_norm (fun i => s i • v i) i

theorem prod_elim_pow {κ : Type} [Fintype κ] {r : ℕ} (blk : κ → Option (Fin r)) (t : Fin r → ℝ) (f d : ℕ)
    (hcard : ∀ i : Fin r, (Finset.univ.filter (fun j => blk j = some i)).card = 2 * d) :
    ∏ j, (blk j).elim 1 t ^ f = (∏ i, t i ^ (f * d)) ^ 2 := by
  rw [← Finset.prod_fiberwise (Finset.univ : Finset κ) blk (fun j => ((blk j).elim 1 t : ℝ) ^ f)]
  have h1 : ∀ o : Option (Fin r), ∏ j ∈ Finset.univ.filter (fun j => blk j = o), (blk j).elim 1 t ^ f =
      (o.elim 1 t ^ f) ^ (Finset.univ.filter (fun j => blk j = o)).card := by
    intro o
    rw [← Finset.prod_const]
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [(Finset.mem_filter.1 hj).2]
  rw [Finset.prod_congr rfl (fun o _ => h1 o), Fintype.prod_option]
  simp only [Option.elim_none, Option.elim_some, one_pow, one_mul, hcard]
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  ring

end GlobalTheory.TorusTheta

namespace GlobalTheory.TorusTheta

theorem theta_torus_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ (r₀ : ℕ) (Xf Yf : Matrix (Fin n) (Fin r₀) E),
    GlobalTheory.SiegelSet.IsWittFrame σ ((1 : E) • X.J.map σ) Xf Yf → ∀ c : ℝ, 0 < c →
    ∀ Φ ∈ schA F (Fin n × Fin d), ∃ (C : ℝ) (k : ℕ), ∀ t ∈ GlobalTheory.SiegelSet.cone r₀ c, ∀ a,
      GlobalTheory.SiegelSet.IsTorusElt σ ((1 : E) • X.J.map σ) Xf Yf t a → ∀ a' : UA σ X.J,
      (a' : GL (Fin n) (AE F E)) = HA.mat (AF F) σ ((1 : E) • X.J.map σ) a → ∀ (y : UA σ X.J) (h : UA σ W.J),
      ‖theta om Φ (a' * y) h‖ ≤ C * ((ht y : ℝ) * ht h) ^ k * ∏ i, t i ^ (Module.finrank ℚ F * d) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP r₀ Xf Yf hWitt c hc Φ hΦ
  obtain ⟨co, blk, hrat, hcard, hact⟩ := GlobalTheory.T.witt_frame_darboux_coordinates F E σ B n d X W M χX χW om r s r' s' hP r₀ Xf Yf hWitt
  obtain ⟨M₁, om₁, e, c₀, hco, hP₁, hc₀, he⟩ := GlobalTheory.T.darboux_coords_rational_points F E σ B n d X W M χX χW om r s r' s' hP co hrat
  obtain ⟨N₀, k₃, C₃, hlat⟩ := GlobalTheory.LatScaleSum.thetaSum_norm_le_pow F (Fin n × Fin d)
  have heΦ := (he Φ hΦ).1
  obtain ⟨C₁, k₁, hdec⟩ := GlobalTheory.T.weilRepresentation_pointwise_archimedeanDecay_bound F E σ B n d X W M₁ χX χW om₁ r s r' s' hP₁ (e Φ) heΦ N₀
  obtain ⟨C₂, k₂, hden⟩ := GlobalTheory.T.schwartz_theta_polynomial_growth F E σ B n d X W M₁ χX χW om₁ r s r' s' hP₁ (e Φ) heΦ
  set c' : ℝ := min 1 c ^ r₀ with hc'def
  have hc'0 : 0 < c' := pow_pos (lt_min one_pos hc) _
  have hc'1 : c' ≤ 1 := pow_le_one₀ (lt_min one_pos hc).le (min_le_left _ _)
  refine ⟨‖c₀‖⁻¹ * |C₃| * (c'⁻¹) ^ N₀ * |C₁| * |C₂| ^ k₃, k₁ + k₂ * k₃, ?_⟩
  intro t htc a hta a' ha' y h
  have tlow : ∀ i, c' ≤ t i := min_pow_le_of_mem_cone hc htc
  have tpos : ∀ i, 0 < t i := fun i => hc'0.trans_le (tlow i)
  set u : Fin n × Fin d → ℝ := fun j => (blk j).elim 1 t with hudef
  have hulow : ∀ j, c' ≤ u j := by
    intro j
    simp only [hudef]
    cases blk j with
    | none => exact hc'1
    | some i => exact tlow i
  have hupos : ∀ j, 0 < u j := fun j => hc'0.trans_le (hulow j)
  obtain ⟨κ, hκ, hom⟩ := GlobalTheory.T.torus_action_model_coordinates F E σ B n d X W M₁ χX χW om₁ r s r' s' hP₁ a' u hupos
    (by rw [hco]; exact hact t tpos a hta a' ha')

  have hΨ0 : om (y, h) Φ ∈ schA F (Fin n × Fin d) := (IsUWeilPair.isUSplitting hP.weil).pres _ _ hΦ
  have hT : om (a', 1) (om (y, h) Φ) ∈ schA F (Fin n × Fin d) := (IsUWeilPair.isUSplitting hP.weil).pres _ _ hΨ0
  obtain ⟨Ψ, hΨdef⟩ : ∃ Ψ, Ψ = om₁ (y, h) (e Φ) := ⟨_, rfl⟩
  have hΨ : Ψ ∈ schA F (Fin n × Fin d) := hΨdef ▸ (IsUWeilPair.isUSplitting hP₁.weil).pres _ _ heΦ
  have hmul : ((a' * y, h) : UA σ X.J × UA σ W.J) = (a', 1) * (y, h) := by
    ext <;> simp
  have hsplit : om (a' * y, h) Φ = om (a', 1) (om (y, h) Φ) := by
    rw [hmul, map_mul, Module.End.mul_apply]
  have heT : e (om (a', 1) (om (y, h) Φ)) = om₁ (a', 1) Ψ := by
    rw [(he _ hΨ0).2.2, (he Φ hΦ).2.2, hΨdef]
  have hthT : thetaSum F (om (a', 1) (om (y, h) Φ)) = c₀⁻¹ * thetaSum F (om₁ (a', 1) Ψ) := by
    rw [← heT, (he _ hT).2.1, ← mul_assoc, inv_mul_cancel₀ hc₀, one_mul]
  have hfun : om₁ (a', 1) Ψ = fun x => κ * Ψ (fun j => infScale F (u j) * x j) := funext (hom Ψ hΨ)
  have hkey : theta om Φ (a' * y) h =
      c₀⁻¹ * (κ * thetaSum F (fun x => Ψ (fun j => infScale F (u j) * x j))) := by
    show thetaSum F (om (a' * y, h) Φ) = _
    rw [hsplit, hthT, hfun]
    unfold thetaSum
    rw [tsum_mul_left]

  have hκ' : ‖κ‖ = ∏ i, t i ^ (Module.finrank ℚ F * d) := by
    have h2 : ‖κ‖ ^ 2 = (∏ i, t i ^ (Module.finrank ℚ F * d)) ^ 2 := by
      rw [hκ]
      exact prod_elim_pow blk t _ d hcard
    have hnn : 0 ≤ ∏ i, t i ^ (Module.finrank ℚ F * d) :=
      Finset.prod_nonneg fun i _ => pow_nonneg (tpos i).le _
    exact (pow_left_inj₀ (norm_nonneg _) hnn two_ne_zero).1 h2

  set P : ℝ := (ht y : ℝ) * ht h with hPdef
  have hP0 : 0 ≤ P := mul_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)
  obtain ⟨m, hm1, hmC, hmint⟩ := hden y h
  have hdecay : ∀ ξ : Fin n × Fin d → F,
      ‖Ψ (fun j => infScale F (u j) * (fun i => algebraMap F (AF F) (ξ i)) j)‖ *
        (1 + ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖) ^ N₀ ≤ (c'⁻¹) ^ N₀ * (C₁ * P ^ k₁) := by
    intro ξ
    beta_reduce
    have h1 := hdec y h (fun j => infScale F (u j) * algebraMap F (AF F) (ξ j))
    rw [← hΨdef] at h1
    have hnorm : c' * ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖ ≤
        ‖fun i => evI F (infScale F (u i) * algebraMap F (AF F) (ξ i))‖ := by
      simp only [evI_infScale_mul]
      exact mul_norm_le_norm_smul hc'0 u hulow _
    have hle : 1 + ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖ ≤
        c'⁻¹ * (1 + ‖fun i => evI F (infScale F (u i) * algebraMap F (AF F) (ξ i))‖) := by
      have hi : 1 ≤ c'⁻¹ := one_le_inv₀ hc'0 |>.2 hc'1
      have h3 : ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖ ≤
          c'⁻¹ * ‖fun i => evI F (infScale F (u i) * algebraMap F (AF F) (ξ i))‖ := by
        rw [le_inv_mul_iff₀ hc'0]; exact hnorm
      nlinarith [norm_nonneg (fun i => evI F (infScale F (u i) * algebraMap F (AF F) (ξ i)))]
    have hpow : (1 + ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖) ^ N₀ ≤
        (c'⁻¹) ^ N₀ * (1 + ‖fun i => evI F (infScale F (u i) * algebraMap F (AF F) (ξ i))‖) ^ N₀ := by
      have h0 : 0 ≤ 1 + ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖ :=
        add_nonneg zero_le_one (norm_nonneg _)
      have h4 := pow_le_pow_left₀ h0 hle N₀
      rw [mul_pow] at h4
      exact h4
    calc ‖Ψ (fun j => infScale F (u j) * algebraMap F (AF F) (ξ j))‖ *
          (1 + ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖) ^ N₀
        ≤ ‖Ψ (fun j => infScale F (u j) * algebraMap F (AF F) (ξ j))‖ *
          ((c'⁻¹) ^ N₀ * (1 + ‖fun i => evI F (infScale F (u i) * algebraMap F (AF F) (ξ i))‖) ^ N₀) :=
          mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
      _ = (c'⁻¹) ^ N₀ * (‖Ψ (fun j => infScale F (u j) * algebraMap F (AF F) (ξ j))‖ *
          (1 + ‖fun i => evI F (infScale F (u i) * algebraMap F (AF F) (ξ i))‖) ^ N₀) := by ring
      _ ≤ (c'⁻¹) ^ N₀ * (C₁ * P ^ k₁) := mul_le_mul_of_nonneg_left h1 (by positivity)
  have hint : ∀ ξ : Fin n × Fin d → F,
      Ψ (fun j => infScale F (u j) * (fun i => algebraMap F (AF F) (ξ i)) j) ≠ 0 →
        ∀ i, IsIntegral ℤ ((m : F) * ξ i) := by
    intro ξ hne
    rw [hΨdef] at hne
    exact hmint _ ξ (fun i => infScale_mul_snd F (u i) _) hne
  have hS := hlat ((c'⁻¹) ^ N₀ * (C₁ * P ^ k₁)) m (fun x => Ψ (fun j => infScale F (u j) * x j)) hm1 hdecay hint

  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hmk : (m : ℝ) ^ k₃ ≤ |C₂| ^ k₃ * P ^ (k₂ * k₃) := by
    rw [pow_mul, ← mul_pow]
    exact pow_le_pow_left₀ hm0 (hmC.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hP0 _))) k₃
  have hS' : ‖thetaSum F (fun x => Ψ (fun j => infScale F (u j) * x j))‖ ≤
      |C₃| * (c'⁻¹) ^ N₀ * |C₁| * |C₂| ^ k₃ * P ^ (k₁ + k₂ * k₃) := by
    refine hS.trans ?_
    calc C₃ * ((c'⁻¹) ^ N₀ * (C₁ * P ^ k₁)) * (m : ℝ) ^ k₃
        ≤ |C₃| * ((c'⁻¹) ^ N₀ * (|C₁| * P ^ k₁)) * (m : ℝ) ^ k₃ := by
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg hm0 _)
          calc C₃ * ((c'⁻¹) ^ N₀ * (C₁ * P ^ k₁)) ≤ |C₃ * ((c'⁻¹) ^ N₀ * (C₁ * P ^ k₁))| := le_abs_self _
            _ = |C₃| * ((c'⁻¹) ^ N₀ * (|C₁| * P ^ k₁)) := by
              rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (c'⁻¹) ^ N₀),
                abs_of_nonneg (pow_nonneg hP0 _)]
      _ ≤ |C₃| * ((c'⁻¹) ^ N₀ * (|C₁| * P ^ k₁)) * (|C₂| ^ k₃ * P ^ (k₂ * k₃)) :=
          mul_le_mul_of_nonneg_left hmk (by positivity)
      _ = |C₃| * (c'⁻¹) ^ N₀ * |C₁| * |C₂| ^ k₃ * P ^ (k₁ + k₂ * k₃) := by ring
  rw [hkey, norm_mul, norm_mul, norm_inv, hκ']
  have hT0 : 0 ≤ ∏ i, t i ^ (Module.finrank ℚ F * d) :=
    Finset.prod_nonneg fun i _ => pow_nonneg (tpos i).le _
  calc ‖c₀‖⁻¹ * ((∏ i, t i ^ (Module.finrank ℚ F * d)) * ‖thetaSum F (fun x => Ψ (fun j => infScale F (u j) * x j))‖)
      ≤ ‖c₀‖⁻¹ * ((∏ i, t i ^ (Module.finrank ℚ F * d)) *
          (|C₃| * (c'⁻¹) ^ N₀ * |C₁| * |C₂| ^ k₃ * P ^ (k₁ + k₂ * k₃))) := by gcongr
    _ = _ := by ring

end GlobalTheory.TorusTheta
end

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_set_witt_frame_schwartz_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ (r₀ : ℕ) (Xf Yf : Matrix (Fin n) (Fin r₀) E),
    GlobalTheory.SiegelSet.IsWittFrame σ ((1 : E) • X.J.map σ) Xf Yf → ∀ c : ℝ, 0 < c →
    ∀ Φ ∈ schA F (Fin n × Fin d), ∃ (C : ℝ) (k : ℕ), ∀ t ∈ GlobalTheory.SiegelSet.cone r₀ c, ∀ a,
      GlobalTheory.SiegelSet.IsTorusElt σ ((1 : E) • X.J.map σ) Xf Yf t a → ∀ a' : UA σ X.J,
      (a' : GL (Fin n) (AE F E)) = HA.mat (AF F) σ ((1 : E) • X.J.map σ) a → ∀ (y : UA σ X.J) (h : UA σ W.J),
      ‖theta om Φ (a' * y) h‖ ≤ C * ((ht y : ℝ) * ht h) ^ k * ∏ i, t i ^ (Module.finrank ℚ F * d) := by
  atlas_forward_decl GlobalTheory.TorusTheta.theta_torus_le
end

section
section
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

namespace GlobalTheory.SiegelTheta

theorem transp {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a : GAd σ ((1 : E) • J.map σ)) :
    ∃ a' : UA σ J, (a' : GL (Fin n) (AE F E)) = HA.mat (AF F) σ ((1 : E) • J.map σ) a := by
  have e := GlobalTheory.SiegelSet.ug_eq_hr (F := F) (J := J) hσ (c := (1 : E)) one_ne_zero
  refine ⟨⟨HA.mat (AF F) σ ((1 : E) • J.map σ) a, ?_⟩, rfl⟩
  have : HA.mat (AF F) σ ((1 : E) • J.map σ) a ∈ HR (AF F) σ ((1 : E) • J.map σ) := a.2
  rw [← e] at this
  exact this

theorem ht_bdd {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) {C₀ K : Set (GAd σ J)} (hC₀ : IsCompact C₀) (hK : IsCompact K) :
    ∃ B : ℝ, ∀ x ∈ C₀, ∀ k ∈ K, (heightGL F (HA.mat (AF F) σ J (x * k)) : ℝ) ≤ B := by
  have hc : Continuous fun q : GAd σ J × GAd σ J => (heightGL F (HA.mat (AF F) σ J (q.1 * q.2)) : ℝ) :=
    NNReal.continuous_coe.comp ((GlobalTheory.Grow.continuous_heightGL F).comp (continuous_subtype_val.comp (continuous_mul : Continuous fun p : GAd σ J × GAd σ J => p.1 * p.2)))
  obtain ⟨B, hB⟩ := ((hC₀.prod hK).image hc).bddAbove
  exact ⟨B, fun x hx k hk => hB ⟨(x, k), ⟨hx, hk⟩, rfl⟩⟩

end GlobalTheory.SiegelTheta

namespace GlobalTheory.SiegelTheta

theorem theta_le_seminorm_height_torus : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ) (hP : IsPair B M χX χW om r s r' s') (r₀ : ℕ) (Xf Yf : Matrix (Fin n) (Fin r₀) E),
    GlobalTheory.SiegelSet.IsWittFrame σ ((1 : E) • X.J.map σ) Xf Yf →
    ∀ (Ω C₀ : Set (GAd σ ((1 : E) • X.J.map σ))) (K : Subgroup (GAd σ ((1 : E) • X.J.map σ))) (c : ℝ),
      IsCompact Ω → IsCompact C₀ → IsCompact (K : Set (GAd σ ((1 : E) • X.J.map σ))) → 0 < c →
      (∀ p ∈ Ω, ∀ t ∈ GlobalTheory.SiegelSet.cone r₀ c, ∀ a, GlobalTheory.SiegelSet.IsTorusElt σ ((1 : E) • X.J.map σ) Xf Yf t a →
        a⁻¹ * p * a ∈ C₀) →
      ∀ φ ∈ SB (Fin n × Fin d → Af F), ∃ (N : ℕ) (C : ℝ) (T : Finset (ℕ × ℕ)),
        ∀ (f : SInf F (Fin n × Fin d)) (h : UA σ W.J) (g : UA σ X.J), ∀ p ∈ Ω, ∀ t ∈ GlobalTheory.SiegelSet.cone r₀ c, ∀ a,
          GlobalTheory.SiegelSet.IsTorusElt σ ((1 : E) • X.J.map σ) Xf Yf t a → ∀ k ∈ K,
          g.1 = HA.mat (AF F) σ ((1 : E) • X.J.map σ) (p * a * k) →
          ‖theta om (pureA F f φ) g h‖ ≤
            C * (T.sup (schwartzSeminormFamily ℂ (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ)) f *
              (ht h : ℝ) ^ N * ∏ i, t i ^ (Module.finrank ℚ F * d) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP r₀ Xf Yf hfr Ω C₀ K c hΩ hC₀ hK hc hconj φ hφ
  have hσ : ∀ x, σ (σ x) = x := GlobalTheory.SiegelSet.sigma_sigma hP.base.cm
  obtain ⟨Bd, hBd⟩ := ht_bdd ((1 : E) • X.J.map σ) hC₀ hK
  let I := {q : UA σ W.J × UA σ X.J × GAd σ ((1 : E) • X.J.map σ) × (Fin r₀ → ℝ) × GAd σ ((1 : E) • X.J.map σ) ×
      GAd σ ((1 : E) • X.J.map σ) // q.2.2.1 ∈ Ω ∧ q.2.2.2.1 ∈ GlobalTheory.SiegelSet.cone r₀ c ∧
      GlobalTheory.SiegelSet.IsTorusElt σ ((1 : E) • X.J.map σ) Xf Yf q.2.2.2.1 q.2.2.2.2.1 ∧ q.2.2.2.2.2 ∈ K ∧
      (q.2.1 : GL (Fin n) (AE F E)) = HA.mat (AF F) σ ((1 : E) • X.J.map σ) (q.2.2.1 * q.2.2.2.2.1 * q.2.2.2.2.2)}
  have hT := fun q : I => GlobalTheory.T.theta_kernel_continuous_functional F E σ B n d X W M χX χW om r s r' s' hP φ hφ q.1.2.1 q.1.1
  choose T hT using hT
  let P : I → ℝ := fun q => ∏ i, q.1.2.2.2.1 i ^ (Module.finrank ℚ F * d)
  have hP0 : ∀ q : I, 0 < P q := fun q => Finset.prod_pos fun i _ => pow_pos (q.2.2.1.1 i) _
  have hpt : ∀ f : SchwartzMap (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ, ∃ (N : ℕ) (C : ℝ), ∀ q : I,
      ‖((P q)⁻¹ • T q) f‖ ≤ C * (ht q.1.1 : ℝ) ^ N := by
    intro f
    obtain ⟨C₁, k₁, h₁⟩ := GlobalTheory.T.siegel_set_witt_frame_schwartz_bound F E σ B n d X W M χX χW om r s r' s' hP r₀ Xf Yf hfr c hc (pureA F f φ)
      (Submodule.subset_span ⟨f, φ, hφ, rfl⟩)
    refine ⟨k₁, |C₁| * (max Bd 0) ^ k₁, fun q => ?_⟩
    obtain ⟨⟨h, g, p, t, a, k⟩, hp, htc, ha, hk, hg⟩ := q
    obtain ⟨a', ha'⟩ := transp hσ X.J a
    have hy : ((a'⁻¹ * g : UA σ X.J) : GL (Fin n) (AE F E)) =
        HA.mat (AF F) σ ((1 : E) • X.J.map σ) ((a⁻¹ * p * a) * k) := by
      have : (a⁻¹ * p * a) * k = a⁻¹ * (p * a * k) := by group
      rw [this]
      change (a' : GL (Fin n) (AE F E))⁻¹ * (g : GL (Fin n) (AE F E)) = _
      rw [ha', hg]
      rfl
    have hty : (ht (a'⁻¹ * g) : ℝ) ≤ max Bd 0 := by
      refine le_trans ?_ (le_max_left _ _)
      show (heightGL F ((a'⁻¹ * g : UA σ X.J) : GL (Fin n) (AE F E)) : ℝ) ≤ Bd
      rw [hy]
      exact hBd _ (hconj p hp t htc a ha) k hk
    have hb := h₁ t htc a ha a' ha' (a'⁻¹ * g) h
    rw [mul_inv_cancel_left] at hb
    have hPq : 0 < ∏ i, t i ^ (Module.finrank ℚ F * d) := Finset.prod_pos fun i _ => pow_pos (htc.1 i) _
    show ‖((∏ i, t i ^ (Module.finrank ℚ F * d))⁻¹ • T _) f‖ ≤ _
    rw [ContinuousLinearMap.smul_apply, ← hT, norm_smul, Real.norm_of_nonneg (inv_pos.2 hPq).le]
    have h0 : (0 : ℝ) ≤ (ht h : ℝ) := NNReal.coe_nonneg _
    have hy0 : (0 : ℝ) ≤ (ht (a'⁻¹ * g) : ℝ) := NNReal.coe_nonneg _
    calc (∏ i, t i ^ (Module.finrank ℚ F * d))⁻¹ * ‖theta om (pureA F f φ) g h‖
        ≤ (∏ i, t i ^ (Module.finrank ℚ F * d))⁻¹ * (C₁ * ((ht (a'⁻¹ * g) : ℝ) * ht h) ^ k₁ *
            ∏ i, t i ^ (Module.finrank ℚ F * d)) := mul_le_mul_of_nonneg_left hb (inv_pos.2 hPq).le
      _ = C₁ * ((ht (a'⁻¹ * g) : ℝ) * ht h) ^ k₁ := by field_simp
      _ ≤ |C₁| * ((max Bd 0) * ht h) ^ k₁ :=
          mul_le_mul (le_abs_self _) (pow_le_pow_left₀ (mul_nonneg hy0 h0) (mul_le_mul_of_nonneg_right hty h0) _)
            (pow_nonneg (mul_nonneg hy0 h0) _) (abs_nonneg _)
      _ = |C₁| * (max Bd 0) ^ k₁ * (ht h : ℝ) ^ k₁ := by rw [mul_pow]; ring
  obtain ⟨N, C, S, hN⟩ := GlobalTheory.T.uniform_schwartz_seminorm_bound (Fin n × Fin d → mixedEmbedding.mixedSpace F) I (fun q => (P q)⁻¹ • T q)
    (fun q => (ht q.1.1 : ℝ)) (fun q => NNReal.coe_nonneg _) hpt
  refine ⟨N, C, S, fun f h g p hp t htc a ha k hk hg => ?_⟩
  let q : I := ⟨(h, g, p, t, a, k), hp, htc, ha, hk, hg⟩
  have e1 : theta om (pureA F f φ) g h = P q • ((P q)⁻¹ • T q f) := by
    rw [smul_smul, mul_inv_cancel₀ (hP0 q).ne', one_smul]
    exact hT q f
  have e2 := hN q f
  simp only [ContinuousLinearMap.smul_apply] at e2
  rw [e1, norm_smul, Real.norm_of_nonneg (hP0 q).le]
  calc P q * ‖(P q)⁻¹ • T q f‖ ≤ P q * (C * (S.sup (schwartzSeminormFamily ℂ _ ℂ)) f * (ht h : ℝ) ^ N) :=
        mul_le_mul_of_nonneg_left e2 (hP0 q).le
    _ = _ := by ring

end GlobalTheory.SiegelTheta
end

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_set_witt_frame_domain : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ) (hP : IsPair B M χX χW om r s r' s') (r₀ : ℕ) (Xf Yf : Matrix (Fin n) (Fin r₀) E),
    GlobalTheory.SiegelSet.IsWittFrame σ ((1 : E) • X.J.map σ) Xf Yf →
    ∀ (Ω C₀ : Set (GAd σ ((1 : E) • X.J.map σ))) (K : Subgroup (GAd σ ((1 : E) • X.J.map σ))) (c : ℝ),
      IsCompact Ω → IsCompact C₀ → IsCompact (K : Set (GAd σ ((1 : E) • X.J.map σ))) → 0 < c →
      (∀ p ∈ Ω, ∀ t ∈ GlobalTheory.SiegelSet.cone r₀ c, ∀ a, GlobalTheory.SiegelSet.IsTorusElt σ ((1 : E) • X.J.map σ) Xf Yf t a →
        a⁻¹ * p * a ∈ C₀) →
      ∀ φ ∈ SB (Fin n × Fin d → Af F), ∃ (N : ℕ) (C : ℝ) (T : Finset (ℕ × ℕ)),
        ∀ (f : SInf F (Fin n × Fin d)) (h : UA σ W.J) (g : UA σ X.J), ∀ p ∈ Ω, ∀ t ∈ GlobalTheory.SiegelSet.cone r₀ c, ∀ a,
          GlobalTheory.SiegelSet.IsTorusElt σ ((1 : E) • X.J.map σ) Xf Yf t a → ∀ k ∈ K,
          g.1 = HA.mat (AF F) σ ((1 : E) • X.J.map σ) (p * a * k) →
          ‖theta om (pureA F f φ) g h‖ ≤
            C * (T.sup (schwartzSeminormFamily ℂ (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ)) f *
              (ht h : ℝ) ^ N * ∏ i, t i ^ (Module.finrank ℚ F * d) := by
  atlas_forward_decl GlobalTheory.SiegelTheta.theta_le_seminorm_height_torus
end
