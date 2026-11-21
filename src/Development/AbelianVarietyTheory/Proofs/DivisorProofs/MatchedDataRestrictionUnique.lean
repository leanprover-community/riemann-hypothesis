import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisAdaptedToCartanInvolution
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupportedAtInfinityAdeleEqZeroOfComplexComponent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanAdeleCMPrescribedEmbeddingValue
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanEigenOrthonormalFrameExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactOneParameterLinesOfLieLines
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealMapsRelevantSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzPreservingOperatorLocalStructure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegralArchimedeanInvariantStatement

section
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.RealLift

theorem exists_atInf_piInf_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (emb : ∀ w : InfinitePlace F, EmbOver E w) (f : InfinitePlace F → ℂ),
    ∃ z : AE F E, At (evI F) z ∧ ∀ w, piInf (emb w) z = f w := by
  intro F E _ _ _ _ _ σ h emb f
  have := h.1

  have him : ∀ (τ : E →+* ℂ) (e : E), σ e ≠ e → (τ e).im ≠ 0 := fun τ e he him => by
    apply he
    apply τ.injective
    rw [h.2.2.2 τ e]
    exact Complex.conj_eq_iff_im.2 him
  by_cases hσ : ∃ e : E, σ e ≠ e
  swap
  · push_neg at hσ
    refine ⟨0, fun u _ => smul_zero u, fun w => ?_⟩
    exfalso
    have := h.2.1
    refine (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (InfinitePlace.mk (emb w).1)))
      (InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => ?_)))
    exact (h.2.2.2 (emb w).1 x).symm.trans (congrArg _ (hσ x))
  obtain ⟨e, he⟩ := hσ
  let lift : ∀ w : InfinitePlace F, ℝ → w.Completion := fun w t =>
    (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm t
  have hlift : ∀ w t, InfinitePlace.Completion.extensionEmbedding w (lift w t) = (t : ℂ) := fun w t => by
    rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (IsTotallyReal.isReal w)]
    exact congrArg _ ((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).apply_symm_apply t)
  let c : InfinitePlace F → ℝ := fun w => (f w).im / ((emb w).1 e).im
  let a : InfinitePlace F → ℝ := fun w => (f w).re - c w * ((emb w).1 e).re
  let A : AF F := ((fun w => lift w (a w) : Ainf F), 0)
  let C : AF F := ((fun w => lift w (c w) : Ainf F), 0)
  refine ⟨A ⊗ₜ[F] (1 : E) + C ⊗ₜ[F] e, fun u hu => ?_, fun w => ?_⟩
  · have hu1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (hu.trans (map_zero _).symm)
    have hA : u * A = 0 := by
      show ((u.1 * A.1, u.2 * (0 : Af F)) : Ainf F × Af F) = ((0, 0) : Ainf F × Af F)
      rw [hu1, zero_mul, mul_zero]
    have hC : u * C = 0 := by
      show ((u.1 * C.1, u.2 * (0 : Af F)) : Ainf F × Af F) = ((0, 0) : Ainf F × Af F)
      rw [hu1, zero_mul, mul_zero]
    rw [smul_add, TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, hA, hC,
      TensorProduct.zero_tmul, TensorProduct.zero_tmul, add_zero]
  · change infEmb (emb w) (compInf F E w (A ⊗ₜ[F] (1 : E) + C ⊗ₜ[F] e)) = f w
    rw [map_add]
    change infEmb (emb w) (evInf F w A ⊗ₜ[F] (1 : E) + evInf F w C ⊗ₜ[F] e) = f w
    rw [map_add, infEmb_tmul, infEmb_tmul, map_one, mul_one]
    change InfinitePlace.Completion.extensionEmbedding w (lift w (a w)) +
      InfinitePlace.Completion.extensionEmbedding w (lift w (c w)) * (emb w).1 e = f w
    rw [hlift, hlift]
    have hne := him (emb w).1 e he
    apply Complex.ext
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero, a]
      ring
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, zero_mul, add_zero, zero_add, c]
      field_simp

end GlobalTheory.RealLift
end

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_supportedAtInfinity_adele_with_complexComponents : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (emb : ∀ w : InfinitePlace F, EmbOver E w) (f : InfinitePlace F → ℂ),
    ∃ z : AE F E, At (evI F) z ∧ ∀ w, piInf (emb w) z = f w := by
  atlas_forward_decl GlobalTheory.RealLift.exists_atInf_piInf_eq
end

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.supportedAtInfinity_adele_eq_zero_of_complexComponents : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (emb : ∀ w : InfinitePlace F, EmbOver E w) (z : AE F E), At (evI F) z →
    (∀ w, piInf (emb w) z = 0) → z = 0 := by
  first | exact @GlobalTheory.AdeleInfInj.eq_zero_of_piInf_eq_zero | exact GlobalTheory.AdeleInfInj.eq_zero_of_piInf_eq_zero | (intros; apply GlobalTheory.AdeleInfInj.eq_zero_of_piInf_eq_zero <;> assumption)
end

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.RealPlaceConj

theorem piInf_cA_eq_star : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (w : InfinitePlace F) (τ : EmbOver E w) (z : AE F E), piInf τ (cA σ z) = star (piInf τ z) := by
  intro F E _ _ _ _ _ σ hσ w τ z

  have hcomp : compInf F E w (cA σ z) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR _ σ (compInf F E w z) := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      simp [cA, compInf, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Algebra.TensorProduct.map_tmul]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

  change infEmb τ (compInf F E w (cA σ z)) = star (infEmb τ (compInf F E w z))
  rw [hcomp, ← GlobalTheory.AdelicU.infEmb_sigR hσ τ]
  rfl

end GlobalTheory.RealPlaceConj
end

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realPlaceComponent_adeleConjugation_eq_complexConj : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (w : InfinitePlace F) (τ : EmbOver E w) (z : AE F E), piInf τ (cA σ z) = star (piInf τ z) := by
  first | exact @GlobalTheory.RealPlaceConj.piInf_cA_eq_star | exact GlobalTheory.RealPlaceConj.piInf_cA_eq_star | (intros; apply GlobalTheory.RealPlaceConj.piInf_cA_eq_star <;> assumption)
end

section
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section
namespace GlobalTheory.ConjCartan

open scoped ComplexOrder in

theorem exists_conj_cartan_matrix : ∀ (n : ℕ) (M θ₁ θ₂ : Matrix (Fin n) (Fin n) ℂ), Mᴴ = M → IsCartan M θ₁ → IsCartan M θ₂ →
    ∃ u v : Matrix (Fin n) (Fin n) ℂ, u * v = 1 ∧ uᵀ * M * u.map star = M ∧ u * θ₁ = θ₂ * u := by
  intro n M θ₁ θ₂ hM h1 h2
  have key : ∀ θ, IsCartan M θ → θ.map star * θ.map star = 1 ∧ (θ.map star)ᴴ * M * θ.map star = M ∧
      (M * θ.map star).PosDef := by
    rintro θ ⟨hθ, hu, hp⟩
    have hS : θ.map star = θᵀᴴ := rfl
    have hT : (θ.map star)ᴴ = θᵀ := by rw [hS, Matrix.conjTranspose_conjTranspose]
    have hSS : θ.map star * θ.map star = 1 := by
      rw [hS, ← Matrix.conjTranspose_mul, ← Matrix.transpose_mul, hθ, Matrix.transpose_one, Matrix.conjTranspose_one]
    have hMS : M * θ.map star = θᵀ * M := by
      calc M * θ.map star = θᵀ * M * θ.map star * θ.map star := by rw [hu]
        _ = θᵀ * M := by rw [Matrix.mul_assoc _ (θ.map star), hSS, Matrix.mul_one]
    have hH : (M * θ.map star)ᴴ = M * θ.map star := by
      rw [Matrix.conjTranspose_mul, hT, hM, hMS]
    refine ⟨hSS, by rw [hT]; exact hu, ?_⟩
    rw [Matrix.posDef_iff_dotProduct_mulVec]
    refine ⟨hH, fun x hx => ?_⟩
    have hx' : star x ≠ 0 := by simpa using hx
    have hre := hp (star x) hx'
    have e1 : star x ⬝ᵥ (M * θ.map star) *ᵥ x = (θ *ᵥ star x) ⬝ᵥ M *ᵥ star (star x) := by
      rw [star_star, hMS, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    have e2 : star (star x ⬝ᵥ (M * θ.map star) *ᵥ x) = star x ⬝ᵥ (M * θ.map star) *ᵥ x := by
      conv_rhs => rw [Matrix.star_dotProduct, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hH]
    rw [Complex.lt_def]
    refine ⟨by rw [e1]; simpa using hre, ?_⟩
    have h3 := congrArg Complex.im e2
    have h4 : (star (star x ⬝ᵥ (M * θ.map star) *ᵥ x)).im = -(star x ⬝ᵥ (M * θ.map star) *ᵥ x).im :=
      Complex.conj_im _
    rw [Complex.zero_im]; linarith
  obtain ⟨hs1, hs2, hs3⟩ := key θ₁ h1
  obtain ⟨ht1, ht2, ht3⟩ := key θ₂ h2
  set S₁ := θ₁.map star
  set S₂ := θ₂.map star
  obtain ⟨p, q, B, B', hBB, hB'B, hBG, hBs⟩ := GlobalTheory.exists_basis_adapted_to_cartan_involution n M S₁ hs1 hs2 hs3
  set D : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := Matrix.fromBlocks 1 0 0 (-1)
  have hDh : Dᴴ = D := by simp [D, Matrix.fromBlocks_conjTranspose]
  have hDD : D * D = 1 := by simp [D, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]
  set T := B' * S₂ * B
  have hTT : T * T = 1 := by
    calc T * T = B' * S₂ * (B * B') * S₂ * B := by simp only [T, Matrix.mul_assoc]
      _ = 1 := by rw [hBB, Matrix.mul_one, Matrix.mul_assoc B', ht1, Matrix.mul_one, hB'B]
  have hinj : Function.Injective B.mulVec := fun x y hxy => by
    have := congrArg (B'.mulVec) hxy
    simpa [Matrix.mulVec_mulVec, hB'B] using this
  have hDT : (D * T).PosDef := by
    have h := ht3.conjTranspose_mul_mul_same hinj
    have e : Bᴴ * (M * S₂) * B = D * T := by
      calc Bᴴ * (M * S₂) * B = Bᴴ * M * (B * B') * S₂ * B := by rw [hBB]; simp only [Matrix.mul_assoc, Matrix.mul_one]
        _ = D * T := by rw [← hBG]; simp only [T, Matrix.mul_assoc]
    rwa [e] at h
  obtain ⟨a, ha1, ha2⟩ := GlobalTheory.cartanInvolution_conj_of_posDef _ D T hDh hDD hTT hDT

  have haL : (D * aᴴ * D) * a = 1 := by simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc aᴴ, ha1, hDD]
  set U := B * a * B'
  set V := B * (D * aᴴ * D) * B'
  have hVU : V * U = 1 := by
    calc V * U = B * (D * aᴴ * D) * (B' * B) * a * B' := by simp only [V, U, Matrix.mul_assoc]
      _ = 1 := by rw [hB'B, Matrix.mul_one, Matrix.mul_assoc B, haL, Matrix.mul_one, hBB]
  have hUU : Uᴴ * M * U = M := by
    have hBh : B'ᴴ * Bᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hBB, Matrix.conjTranspose_one]
    calc Uᴴ * M * U = B'ᴴ * (aᴴ * (Bᴴ * M * B) * a) * B' := by
          simp only [U, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = B'ᴴ * (Bᴴ * M * B) * B' := by rw [hBG, ha1]
      _ = (B'ᴴ * Bᴴ) * M * (B * B') := by simp only [Matrix.mul_assoc]
      _ = M := by rw [hBh, hBB, Matrix.one_mul, Matrix.mul_one]
  have hB'S : B' * S₁ = D * B' := by
    calc B' * S₁ = B' * S₁ * (B * B') := by rw [hBB, Matrix.mul_one]
      _ = B' * (S₁ * B) * B' := by simp only [Matrix.mul_assoc]
      _ = B' * (B * D) * B' := congrArg (fun Z => B' * Z * B') hBs
      _ = (B' * B) * D * B' := by simp only [Matrix.mul_assoc]
      _ = D * B' := by rw [hB'B, Matrix.one_mul]
  have hUS : U * S₁ = S₂ * U := by
    calc U * S₁ = B * (a * D) * B' := by simp only [U, Matrix.mul_assoc, hB'S]
      _ = B * (T * a) * B' := by rw [ha2]
      _ = (B * B') * S₂ * (B * a * B') := by simp only [T, Matrix.mul_assoc]
      _ = S₂ * U := by rw [hBB, Matrix.one_mul]
  refine ⟨U.map star, V.map star, ?_, ?_, ?_⟩
  · have hUV : U * V = 1 := mul_eq_one_comm.1 hVU
    have : (U * V).map star = (1 : Matrix (Fin n) (Fin n) ℂ).map star := by rw [hUV]
    rw [show (1 : Matrix (Fin n) (Fin n) ℂ) = (1 : Matrix (Fin n) (Fin n) ℂ).map star by simp, ← this]; ext i j; simp [Matrix.mul_apply, star_sum]
  · have e : (U.map star)ᵀ = Uᴴ := rfl
    rw [e, show (U.map star).map star = U by ext i j; simp, hUU]
  · have : (U * S₁).map star = (S₂ * U).map star := by rw [hUS]
    have e1 : (U * S₁).map star = U.map star * θ₁ := by ext i j; simp [S₁, Matrix.mul_apply, star_sum]
    have e2 : (S₂ * U).map star = θ₂ * U.map star := by ext i j; simp [S₂, Matrix.mul_apply, star_sum]
    rw [← e1, ← e2, this]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem piInf_inclR {w : InfinitePlace F} (τ : EmbOver E w) (x : E) : piInf τ (inclR (F := F) (AF F) x) = τ.1 x := by
  simp [piInf, inclR, compInf, infEmb_tmul]

variable (F E) in

def archIdeal : Ideal (AE F E) where
  carrier := {z | At (evI F) z}
  add_mem' := fun {a b} ha hb u hu => by rw [smul_add, ha u hu, hb u hu, add_zero]
  zero_mem' := fun u _ => smul_zero u
  smul_mem' := fun c z hz u hu => by
    rw [smul_eq_mul, ← mul_smul_comm, hz u hu, mul_zero]

theorem cA_mem_archIdeal (σ : E →ₐ[F] E) {z : AE F E} (hz : z ∈ archIdeal F E) : cA σ z ∈ archIdeal F E :=
  fun u hu => by rw [← map_smul, hz u hu, map_zero]

end GlobalTheory.ConjCartan

namespace GlobalTheory.ConjCartan

theorem mapMatrix_transpose {R S : Type} [Semiring R] [Semiring S] (f : R →+* S) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) : f.mapMatrix Aᵀ = (f.mapMatrix A)ᵀ := rfl

theorem conj_cartan_arch : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n r s : ℕ) (X Y : Spc F E n), B.IsGood σ → X.IsHerm σ B r s → (reS X Y).IsHerm σ B r s →
    ∃ g ∈ UAt σ X (evI F), ∀ w, (mat g).map (piInf (B.emb w)) * X.θ w = Y.θ w * (mat g).map (piInf (B.emb w)) := by
  intro F E _ _ _ _ _ σ B n r s X Y hB hX hY
  have cm := hB.cm
  have hM : ∀ w, (X.J.map (B.emb w).1)ᴴ = X.J.map (B.emb w).1 := fun w => by
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.map_apply]
    rw [← cm.2.2.2 (B.emb w).1, hX.herm]
  have hU := fun w => exists_conj_cartan_matrix n _ (X.θ w) (Y.θ w) (hM w) (hX.cartan w) (hY.cartan w)
  choose u v huv hun hint using hU
  choose lift hlat hlev using GlobalTheory.T.exists_supportedAtInfinity_adele_with_complexComponents F E σ cm B.emb
  let π := Ideal.Quotient.mk (archIdeal F E)
  let Dm : Matrix (Fin n) (Fin n) (AE F E) := Matrix.of fun i j => lift fun w => (u w - 1) i j
  let Dv : Matrix (Fin n) (Fin n) (AE F E) := Matrix.of fun i j => lift fun w => (v w - 1) i j
  have hDm : π.mapMatrix Dm = 0 := by
    ext i j; exact Ideal.Quotient.eq_zero_iff_mem.2 (hlat _)
  have hDv : π.mapMatrix Dv = 0 := by
    ext i j; exact Ideal.Quotient.eq_zero_iff_mem.2 (hlat _)
  have hDc : π.mapMatrix ((cA σ).toRingHom.mapMatrix Dm) = 0 := by
    ext i j; exact Ideal.Quotient.eq_zero_iff_mem.2 (cA_mem_archIdeal σ (hlat _))
  have hDmw : ∀ w, (piInf (B.emb w)).mapMatrix Dm = u w - 1 := fun w => by
    ext i j; exact hlev _ w
  have hDvw : ∀ w, (piInf (B.emb w)).mapMatrix Dv = v w - 1 := fun w => by
    ext i j; exact hlev _ w
  have zero : ∀ Z : Matrix (Fin n) (Fin n) (AE F E), π.mapMatrix Z = 0 → (∀ w, (piInf (B.emb w)).mapMatrix Z = 0) → Z = 0 := by
    intro Z h1 h2; ext i j
    exact GlobalTheory.T.supportedAtInfinity_adele_eq_zero_of_complexComponents F E σ cm B.emb _ (Ideal.Quotient.eq_zero_iff_mem.1 (congrFun (congrFun h1 i) j))
      (fun w => congrFun (congrFun (h2 w) i) j)
  have hGH : (1 + Dm) * (1 + Dv) = 1 := by
    refine sub_eq_zero.1 (zero _ ?_ fun w => ?_)
    · rw [map_sub, map_mul, map_add, map_add, map_one, hDm, hDv]; simp
    · rw [map_sub, map_mul, map_add, map_add, map_one, hDmw, hDvw, add_sub_cancel, add_sub_cancel, huv w, sub_self]
  let g0 : GL (Fin n) (AE F E) := ⟨1 + Dm, 1 + Dv, hGH, mul_eq_one_comm.1 hGH⟩
  have hcw : ∀ w, (piInf (B.emb w)).mapMatrix ((cA σ).toRingHom.mapMatrix Dm) = (u w).map star - 1 := fun w => by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [show (cA σ).toRingHom (Dm i j) = cA σ (Dm i j) from rfl, GlobalTheory.T.realPlaceComponent_adeleConjugation_eq_complexConj F E σ cm w (B.emb w)]
    simp only [Dm, Matrix.of_apply]
    rw [hlev]
    simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.map_apply, star_sub]
    split_ifs <;> simp
  have hJw : ∀ w, (piInf (B.emb w)).mapMatrix (incM F X.J) = X.J.map (B.emb w).1 := fun w => by
    ext i j; simp [incM, piInf_inclR]
  have hUG : g0 ∈ UG (cA σ) (incM F X.J) := by
    change (1 + Dm)ᵀ * incM F X.J * (cA σ).toRingHom.mapMatrix (1 + Dm) = incM F X.J
    rw [map_add, map_one]
    refine sub_eq_zero.1 (zero _ ?_ fun w => ?_)
    · rw [map_sub, map_mul, map_mul, mapMatrix_transpose, map_add, map_add, map_one, hDm, hDc]; simp
    · rw [map_sub, map_mul, map_mul, mapMatrix_transpose, map_add, map_add, map_one, hDmw, hcw, hJw,
        add_sub_cancel, add_sub_cancel, hun w, sub_self]
  refine ⟨⟨g0, hUG⟩, ?_, fun w => ?_⟩
  · intro a ha
    show a • ((1 + Dm) - 1) = 0
    ext i j
    simp only [add_sub_cancel_left, Matrix.smul_apply, Matrix.zero_apply]
    exact hlat _ a ha
  · have : (mat (⟨g0, hUG⟩ : UA σ X.J)).map (piInf (B.emb w)) = u w := by
      show (piInf (B.emb w)).mapMatrix (1 + Dm) = u w
      rw [map_add, map_one, hDmw]; abel
    rw [this]; exact hint w

end GlobalTheory.ConjCartan
end
end

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cartan_involution_systems_conj_archimedean_unitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n r s : ℕ) (X Y : Spc F E n), B.IsGood σ → X.IsHerm σ B r s → (reS X Y).IsHerm σ B r s →
    ∃ g ∈ UAt σ X (evI F), ∀ w, (mat g).map (piInf (B.emb w)) * X.θ w = Y.θ w * (mat g).map (piInf (B.emb w)) := by
  atlas_forward_decl GlobalTheory.ConjCartan.conj_cartan_arch
end

section
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.CartanConjSkew

open scoped Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem incM_map_piInf {n m : Type} (J : Matrix n m E) {w : InfinitePlace F} (τ : EmbOver E w) :
    (incM F J).map (piInf τ) = J.map τ.1 := by
  ext i j
  simp [incM, piInf, compInf, inclR, infEmb_tmul]

theorem exists_mat_at {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    {m k : Type} (z : InfinitePlace F → Matrix m k ℂ) :
    ∃ u : Matrix m k (AE F E), At (evI F) u ∧ ∀ w, u.map (piInf (τ w)) = z w := by
  choose a ha using fun i j => GlobalTheory.PolRangeInf.exists_at_inf_values hcm τ (fun w => z w i j)
  refine ⟨Matrix.of a, fun x hx => ?_, fun w => ?_⟩
  · ext i j
    simp only [Matrix.smul_apply, Matrix.of_apply, Matrix.zero_apply]
    exact (ha i j).1 x hx
  · ext i j
    simp [(ha i j).2 w]

theorem mat_eq_zero {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    {m k : Type} (D : Matrix m k (AE F E)) (hD : At (evI F) D) (h0 : ∀ w, D.map (piInf (τ w)) = 0) : D = 0 := by
  ext i j
  refine GlobalTheory.RealLift.KLineProof.eq_zero_of_piInf hcm τ (D i j) (fun u hu => ?_) (fun w => ?_)
  · have := congrFun (congrFun (hD u hu) i) j
    simpa using this
  · have := congrFun (congrFun (h0 w) i) j
    simpa using this

theorem at_add {m k : Type} {D D' : Matrix m k (AE F E)} (hD : At (evI F) D) (hD' : At (evI F) D') :
    At (evI F) (D + D') := by
  intro u hu; rw [smul_add, hD u hu, hD' u hu, add_zero]

theorem at_mul_left {m k l : Type} [Fintype k] {D : Matrix m k (AE F E)} (hD : At (evI F) D) (N : Matrix k l (AE F E)) :
    At (evI F) (D * N) := by
  intro u hu; rw [← Matrix.smul_mul, hD u hu, Matrix.zero_mul]

theorem at_mul_right {m k l : Type} [Fintype k] {D : Matrix k l (AE F E)} (hD : At (evI F) D) (N : Matrix m k (AE F E)) :
    At (evI F) (N * D) := by
  intro u hu; rw [← Matrix.mul_smul, hD u hu, Matrix.mul_zero]

theorem at_transpose {m k : Type} {D : Matrix m k (AE F E)} (hD : At (evI F) D) : At (evI F) Dᵀ := by
  intro u hu; rw [← Matrix.transpose_smul, hD u hu, Matrix.transpose_zero]

theorem at_map_cA (σ : E →ₐ[F] E) {m k : Type} {D : Matrix m k (AE F E)} (hD : At (evI F) D) :
    At (evI F) (D.map (cA σ)) := by
  intro u hu
  ext i j
  have := congrFun (congrFun (hD u hu) i) j
  simp only [Matrix.smul_apply, Matrix.zero_apply, Matrix.map_apply] at this ⊢
  rw [← map_smul, this, map_zero]

theorem map_cA_piInf {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) {m k : Type}
    (D : Matrix m k (AE F E)) : (D.map (cA σ)).map (piInf τ) = (D.map (piInf τ)).map star := by
  ext i j
  simp [GlobalTheory.RealLift.KLineProof.piInf_cA hcm]

theorem cartan_conj {n r s : ℕ} (M θ₁ θ₂ : Matrix (Fin n) (Fin n) ℂ) (hs : HasSig M r s) (h₁ : IsCartan M θ₁)
    (h₂ : IsCartan M θ₂) :
    ∃ u v : Matrix (Fin n) (Fin n) ℂ, u * v = 1 ∧ uᵀ * M * u.map star = M ∧ u * θ₁ = θ₂ * u := by
  obtain ⟨A₁, hF₁, hA₁⟩ := GlobalTheory.T.cartanEigen_orthonormalFrame_exists n r s M θ₁ hs h₁
  obtain ⟨A₂, hF₂, hA₂⟩ := GlobalTheory.T.cartanEigen_orthonormalFrame_exists n r s M θ₂ hs h₂
  obtain ⟨A₁', h11, h12⟩ := GlobalTheory.RealLift.KLineProof.frame_inv hF₁
  obtain ⟨A₂', h21, h22⟩ := GlobalTheory.RealLift.KLineProof.frame_inv hF₂
  refine ⟨A₂ * A₁', A₁ * A₂', ?_, ?_, ?_⟩
  · calc A₂ * A₁' * (A₁ * A₂') = A₂ * (A₁' * A₁) * A₂' := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h12, Matrix.mul_one, h21]
  · have e1 := hF₁.1
    have e2 := hF₂.1
    rw [Matrix.transpose_mul, GlobalTheory.RealLift.KLineProof.map_star_mul]
    calc A₁'ᵀ * A₂ᵀ * M * (A₂.map star * A₁'.map star)
        = A₁'ᵀ * (A₂ᵀ * M * A₂.map star) * A₁'.map star := by simp only [Matrix.mul_assoc]
      _ = A₁'ᵀ * (A₁ᵀ * M * A₁.map star) * A₁'.map star := by rw [e2, e1]
      _ = (A₁ * A₁')ᵀ * M * (A₁ * A₁').map star := by
          rw [Matrix.transpose_mul, GlobalTheory.RealLift.KLineProof.map_star_mul]; simp only [Matrix.mul_assoc]
      _ = M := by
          rw [h11, Matrix.transpose_one, Matrix.map_one _ (star_zero _) (star_one _), Matrix.one_mul, Matrix.mul_one]
  · have k1 : A₁' * θ₁ = Formalism.BasicNotions.TH.Jm r s * A₁' := by
      calc A₁' * θ₁ = A₁' * θ₁ * (A₁ * A₁') := by rw [h11, Matrix.mul_one]
        _ = A₁' * (θ₁ * A₁) * A₁' := by simp only [Matrix.mul_assoc]
        _ = (A₁' * A₁) * Formalism.BasicNotions.TH.Jm r s * A₁' := by rw [hA₁]; simp only [Matrix.mul_assoc]
        _ = Formalism.BasicNotions.TH.Jm r s * A₁' := by rw [h12, Matrix.one_mul]
    calc A₂ * A₁' * θ₁ = A₂ * (A₁' * θ₁) := Matrix.mul_assoc _ _ _
      _ = A₂ * Formalism.BasicNotions.TH.Jm r s * A₁' := by rw [k1, Matrix.mul_assoc]
      _ = θ₂ * (A₂ * A₁') := by rw [← hA₂, Matrix.mul_assoc]

end GlobalTheory.CartanConjSkew

namespace GlobalTheory.CartanConjSkew

open scoped Matrix

theorem conj_skew : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n r s : ℕ) (X Y : Spc F E n), B.IsGood σ → X.IsSkew σ B r s → (reS X Y).IsSkew σ B r s →
    ∃ g ∈ UAt σ X (evI F), ∀ w, (mat g).map (piInf (B.emb w)) * X.θ w = Y.θ w * (mat g).map (piInf (B.emb w)) := by
  intro F E _ _ _ _ _ σ B n r s X Y hB hX hY
  have hcm := hB.cm
  have key : ∀ w, ∃ u v : Matrix (Fin n) (Fin n) ℂ, u * v = 1 ∧
      uᵀ * X.J.map (B.emb w).1 * u.map star = X.J.map (B.emb w).1 ∧ u * X.θ w = Y.θ w * u := by
    intro w
    obtain ⟨u, v, huv, hu, hθ⟩ := cartan_conj (Complex.I • X.J.map (B.emb w).1) (X.θ w) (Y.θ w) (hX.sig w)
      (hX.cartan w) (hY.cartan w)
    refine ⟨u, v, huv, ?_, hθ⟩
    rw [Matrix.mul_smul, Matrix.smul_mul] at hu
    exact smul_right_injective _ Complex.I_ne_zero hu
  choose u v huv hu hθ using key
  obtain ⟨G, hGat, hG⟩ := exists_mat_at hcm B.emb (fun w => u w - 1)
  obtain ⟨H, hHat, hH⟩ := exists_mat_at hcm B.emb (fun w => v w - 1)
  have hmap1 : ∀ w, (1 : Matrix (Fin n) (Fin n) (AE F E)).map (piInf (B.emb w)) = 1 :=
    fun w => Matrix.map_one _ (map_zero _) (map_one _)
  have hgmap : ∀ w, (1 + G).map (piInf (B.emb w)) = u w := by
    intro w; rw [Matrix.map_add _ (map_add _), hmap1, hG]; abel
  have hhmap : ∀ w, (1 + H).map (piInf (B.emb w)) = v w := by
    intro w; rw [Matrix.map_add _ (map_add _), hmap1, hH]; abel
  have hgh : (1 + G) * (1 + H) = 1 := by
    have h0 : (1 + G) * (1 + H) - 1 = 0 := by
      apply mat_eq_zero hcm B.emb
      · have e : (1 + G) * (1 + H) - 1 = G + H + G * H := by noncomm_ring
        rw [e]; exact at_add (at_add hGat hHat) (at_mul_left hGat H)
      · intro w
        rw [Matrix.map_sub _ (map_sub _), Matrix.map_mul, hgmap, hhmap, hmap1, huv, sub_self]
    exact sub_eq_zero.1 h0
  have hhg : (1 + H) * (1 + G) = 1 := (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).1 hgh
  let g0 : GL (Fin n) (AE F E) := ⟨1 + G, 1 + H, hgh, hhg⟩
  have hmem : g0 ∈ UG (cA σ) (incM F X.J) := by
    show (1 + G)ᵀ * incM F X.J * (1 + G).map (cA σ) = incM F X.J
    have h0 : (1 + G)ᵀ * incM F X.J * (1 + G).map (cA σ) - incM F X.J = 0 := by
      apply mat_eq_zero hcm B.emb
      · have e : (1 + G)ᵀ * incM F X.J * (1 + G).map (cA σ) - incM F X.J =
            Gᵀ * incM F X.J + incM F X.J * G.map (cA σ) + Gᵀ * incM F X.J * G.map (cA σ) := by
          rw [Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_add, Matrix.transpose_one]
          noncomm_ring
        rw [e]
        exact at_add (at_add (at_mul_left (at_transpose hGat) _) (at_mul_right (at_map_cA σ hGat) _))
          (at_mul_right (at_map_cA σ hGat) _)
      · intro w
        rw [Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, map_cA_piInf hcm, hgmap,
          incM_map_piInf, hu, sub_self]
    exact sub_eq_zero.1 h0
  refine ⟨⟨g0, hmem⟩, ?_, fun w => ?_⟩
  · show At (evI F) ((1 + G) - 1)
    rw [add_sub_cancel_left]; exact hGat
  · show (1 + G).map (piInf (B.emb w)) * X.θ w = Y.θ w * (1 + G).map (piInf (B.emb w))
    rw [hgmap]; exact hθ w

end GlobalTheory.CartanConjSkew
end
end

section
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.skewHermitian_cartanInvolutionSystems_conjugate_archimedean : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n r s : ℕ) (X Y : Spc F E n), B.IsGood σ → X.IsSkew σ B r s → (reS X Y).IsSkew σ B r s →
    ∃ g ∈ UAt σ X (evI F), ∀ w, (mat g).map (piInf (B.emb w)) * X.θ w = Y.θ w * (mat g).map (piInf (B.emb w)) := by
  first | exact @GlobalTheory.CartanConjSkew.conj_skew | exact GlobalTheory.CartanConjSkew.conj_skew | (intros; apply GlobalTheory.CartanConjSkew.conj_skew <;> assumption)
end

section
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_maps_relevant_space : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ (V : Spc F E a) (V' : Spc F E a') (W : Spc F E (a + a')) (R₂ : RealMaps F a a'),
    IsTriple B (reG G V V' W) X om om' → IsRealMaps B (reG G V V' W) om om' R₂ →
    ∀ g ∈ UAt σ G.V (evI F), ∀ g' ∈ UAt σ G.V' (evI F), ∀ h ∈ UAt σ G.W (evI F),
    (∀ w, (mat g).map (piInf (B.emb w)) * G.V.θ w = V.θ w * (mat g).map (piInf (B.emb w))) →
    (∀ w, (mat g').map (piInf (B.emb w)) * G.V'.θ w = V'.θ w * (mat g').map (piInf (B.emb w))) →
    (∀ w, (mat h).map (piInf (B.emb w)) * G.W.θ w = W.θ w * (mat h).map (piInf (B.emb w))) →
    ∃ R₃ : RealMaps F a a', IsRealMaps B G om om' R₃ ∧ ∀ (Rf : FinMaps F a a') Φ Φ', PolMatch B G X R₃ Rf Φ Φ' →
        PolMatch B (reG G V V' W) X R₂ Rf (om (g, h) Φ) (om' (g', h) Φ') := by
  first | exact @GlobalTheory.MajTransport.transport | exact GlobalTheory.MajTransport.transport | (intros; apply GlobalTheory.MajTransport.transport <;> assumption)
end

section
section
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section
namespace GlobalTheory.ArchComm
open Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def finOne : AF F := ((0 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F))

theorem evI_finOne : evI F (finOne (F := F)) = 0 :=
  show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0 from map_zero _

theorem evFin_finOne (v : Pl F) : evFin F v finOne = 1 := by
  show evalV F v (sndA F finOne) = 1
  have : sndA F (finOne (F := F)) = 1 := rfl
  rw [this, map_one]

theorem evFin_one_sub_finOne (v : Pl F) : evFin F v (1 - finOne) = 0 := by
  rw [map_sub, map_one, evFin_finOne, sub_self]

section Mat
variable {m n k : ℕ}

theorem mul_eq_zero_of_at {z : Matrix (Fin m) (Fin n) (AE F E)} (hz : At (evI F) z) {v : Pl F}
    {w : Matrix (Fin n) (Fin k) (AE F E)} (hw : At (evFin F v) w) : z * w = 0 := by
  have h1 : w = (finOne (F := F)) • w := by
    have := hw (1 - finOne (F := F)) (evFin_one_sub_finOne v)
    rwa [sub_smul, one_smul, sub_eq_zero] at this
  have h2 : (finOne (F := F)) • z = 0 := hz finOne evI_finOne
  rw [h1, Matrix.mul_smul, ← Matrix.smul_mul, h2, Matrix.zero_mul]

theorem mul_transpose_eq_zero_of_at {z : Matrix (Fin k) (Fin n) (AE F E)} (hz : At (evI F) z) {v : Pl F}
    {w : Matrix (Fin m) (Fin n) (AE F E)} (hw : At (evFin F v) w) : w * zᵀ = 0 := by
  have h1 : w = (finOne (F := F)) • w := by
    have := hw (1 - finOne (F := F)) (evFin_one_sub_finOne v)
    rwa [sub_smul, one_smul, sub_eq_zero] at this
  have h2 : (finOne (F := F)) • z = 0 := hz finOne evI_finOne
  rw [h1, Matrix.smul_mul, ← Matrix.mul_smul, ← Matrix.transpose_smul, h2, Matrix.transpose_zero, Matrix.mul_zero]

end Mat

variable {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

theorem actAB_eq_of_at {g : UA σ X.J} {h : UA σ W.J} (hg : g ∈ UAt σ X (evI F)) (hh : h ∈ UAt σ W (evI F)) {v : Pl F}
    {w : Matrix (Fin n) (Fin d) (AE F E)} (hw : At (evFin F v) w) : actAB (cA σ) (g, h) w = w := by
  show mat g * w * (mat h)ᵀ = w
  have e1 : mat g * w = w := by
    have := mul_eq_zero_of_at (k := d) hg hw
    rwa [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at this
  have e2 : w * (mat h)ᵀ = w := by
    have := mul_transpose_eq_zero_of_at (m := n) hh hw
    rwa [Matrix.transpose_sub, Matrix.transpose_one, Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at this
  rw [e1, e2]

theorem weil_rho_comm {M : Model σ X W} {ψ : AddChar (AF F) ℂ} {χX χW : Chr F E} {om : Rep σ X W}
    (hW : M.IsWeil ψ χX χW om) {g : UA σ X.J} {h : UA σ W.J} (hg : g ∈ UAt σ X (evI F)) (hh : h ∈ UAt σ W (evI F))
    (v : Pl F) (w : Matrix (Fin n) (Fin d) (AE F E)) (hw : At (evFin F v) w) (Φ : (Fin n × Fin d → AF F) → ℂ)
    (hΦ : Φ ∈ schA F (Fin n × Fin d)) : om (g, h) (M.co.rho ψ w Φ) = M.co.rho ψ w (om (g, h) Φ) := by
  rw [(IsUWeilPair.isUSplitting hW).impl (g, h) w Φ hΦ, actAB_eq_of_at hg hh hw]

end GlobalTheory.ArchComm

namespace GlobalTheory.ThK

theorem so_stable_arch : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ g' ∈ UAt σ G.V' (evI F), ∀ h ∈ UAt σ G.W (evI F), ∀ Φ' ∈ G.M'.So B.ψ B.τ₁,
      om' (g', h) Φ' ∈ G.M'.So B.ψ B.τ₁ := by
  intro hK F E _ _ _ _ _ σ B a a' G X om om' hT g' hg' h hh Φ' hΦ'
  have hS := IsUWeilPair.isUSplitting hT.weil'
  unfold Model.So at hΦ' ⊢
  refine (Submodule.span_le (p := (Submodule.span ℂ _).comap (om' (g', h)))).2 ?_ hΦ'
  rintro _ ⟨f, φ, hφ, hcof, h1, rfl⟩
  obtain ⟨f₁, hf₁⟩ := GlobalTheory.T.schwartz_preserving_operator_local_structure hK.base F E σ B a' (a + a') G.V' G.W G.M' _ _ _ _ hT.base hT.geo.hV' hT.geo.hW hT.geo.hM'
    (om' (g', h)) (fun Φ hΦ => hS.pres (g', h) Φ hΦ)
    (fun v w hw Φ hΦ => GlobalTheory.ArchComm.weil_rho_comm hT.weil' hg' hh v w hw Φ hΦ) f φ hφ hcof
  rw [SetLike.mem_coe, Submodule.mem_comap, hf₁]
  exact Submodule.subset_span ⟨f₁, φ, hφ, hcof, h1, rfl⟩

end GlobalTheory.ThK
end
end

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.so_type_stable_archimedean : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ g' ∈ UAt σ G.V' (evI F), ∀ h ∈ UAt σ G.W (evI F), ∀ Φ' ∈ G.M'.So B.ψ B.τ₁,
      om' (g', h) Φ' ∈ G.M'.So B.ψ B.τ₁ := by
  atlas_forward_decl GlobalTheory.ThK.so_stable_arch
end

section
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.ThKRealConj

theorem realMaps_transport : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ (V : Spc F E a) (V' : Spc F E a') (W : Spc F E (a + a')) (R₂ : RealMaps F a a'),
    IsTriple B (reG G V V' W) X om om' → IsRealMaps B (reG G V V' W) om om' R₂ →
    ∀ g ∈ UAt σ G.V (evI F), ∀ g' ∈ UAt σ G.V' (evI F), ∀ h ∈ UAt σ G.W (evI F),
    (∀ w, (mat g).map (piInf (B.emb w)) * G.V.θ w = V.θ w * (mat g).map (piInf (B.emb w))) →
    (∀ w, (mat g').map (piInf (B.emb w)) * G.V'.θ w = V'.θ w * (mat g').map (piInf (B.emb w))) →
    (∀ w, (mat h).map (piInf (B.emb w)) * G.W.θ w = W.θ w * (mat h).map (piInf (B.emb w))) →
    ∃ R₃ : RealMaps F a a', IsRealMaps B G om om' R₃ ∧ ∀ (Rf : FinMaps F a a') Φ Φ', PolMatch B G X R₃ Rf Φ Φ' →
        PolMatch B (reG G V V' W) X R₂ Rf (om (g, h) Φ) (om' (g', h) Φ') :=
  GlobalTheory.T.real_maps_relevant_space

theorem soLoc_reG' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (G : Geo σ a a') (V : Spc F E a) (V' : Spc F E a') (W : Spc F E (a + a')) (ψ : AddChar (AF F) ℂ) {v : Pl F}
    (t : E →ₐ[F] Fv F v) : (reG G V V' W).M'.SoLoc ψ t = G.M'.SoLoc ψ t := by
  ext φ
  simp only [Model.SoLoc, Model.IsLinBar, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, ι, ⟨a, b, c⟩, h2⟩; exact ⟨h1, ι, ⟨a, b, c⟩, h2⟩
  · rintro ⟨h1, ι, ⟨a, b, c⟩, h2⟩; exact ⟨h1, ι, ⟨a, b, c⟩, h2⟩

theorem so_reG' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (G : Geo σ a a') (V : Spc F E a) (V' : Spc F E a') (W : Spc F E (a + a')) (ψ : AddChar (AF F) ℂ) {v : Pl F}
    (t : E →ₐ[F] Fv F v) : (reG G V V' W).M'.So ψ t = G.M'.So ψ t := by
  unfold Model.So
  rw [soLoc_reG']
  rfl

end GlobalTheory.ThKRealConj
end
