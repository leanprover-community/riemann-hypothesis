import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHeisenbergLineDerivativeFormula
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsComplexStructureGaussVacuumFockEquations
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteWeightComplementaryArchimedeanSchwar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairInfApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianEvaluationGauss
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchimedeanPairNegativeSymplecticPairing
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchwartzCexpNegForm
import GroundTheory.GlobalFields.TateThesis.GaussianSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOfClosedSubmoduleGaussianConvolution
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchwartzGaussWidth

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ArchSch

namespace GlobalTheory.ArchSch

theorem mixedTracePairing_nondegenerate_left {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (x : κ → mixedEmbedding.mixedSpace F) (hx : ∀ y, trP F κ x y = 0) : x = 0 := by
  classical
  funext i
  refine GlobalTheory.ArchUniq.Coord.eq_zero_of_trace _ fun b => ?_
  have := hx (Pi.single i b)
  rwa [mixedTracePairing_apply, Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp), Pi.single_eq_same] at this

theorem mixedTracePairing_nondegenerate_right {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (y : κ → mixedEmbedding.mixedSpace F) (hy : ∀ x, trP F κ x y = 0) : y = 0 := by
  classical
  funext i
  refine GlobalTheory.ArchUniq.Coord.eq_zero_of_trace _ fun b => ?_
  have := hy (Pi.single i b)
  rwa [mixedTracePairing_apply, Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp), Pi.single_eq_same, mul_comm] at this

theorem mixedTracePairing_nondegenerate : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], (trP F κ).Nondegenerate := by
  intro F _ _ κ _
  refine ⟨fun x hx => mixedTracePairing_nondegenerate_left (F := F) (κ := κ) x hx, fun y hy => mixedTracePairing_nondegenerate_right (F := F) (κ := κ) y hy⟩

end GlobalTheory.ArchSch
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

noncomputable section

namespace GlobalTheory.ThK.EvAt0.PlaneQ

theorem trace_symp_neg_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (τ : ∀ w : InfinitePlace F, EmbOver E w) (n d : ℕ) (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E)
      (u v : Matrix (Fin n) (Fin d) (AE F E)),
      Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (symp (R := AF F) (cA σ) (-1) (incM F JX) (incM F JW) u v)) =
        ∑ w, -2 * (∑ i, ∑ j, ∑ k, ∑ l, piInf (τ w) (u i j) * (τ w).1 (JX i k) * (τ w).1 (JW j l) *
          star (piInf (τ w) (v k l))).re := by
  intro F E _ _ _ _ _ σ hCM τ n d JX JW u v
  haveI : IsTotallyReal F := hCM.1
  rw [trace_rho]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [symp, rho_trace hCM (τ w)]
  simp only [map_mul, map_neg, map_one, hTens, map_sum, incM, Matrix.map_apply, piInf_inclR,
    GlobalTheory.WrongSignPair.piInf_cA hCM, neg_one_mul, Complex.neg_re]
  ring
end PlaneQ
end EvAt0
end ThK
end GlobalTheory
end
end

section
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

namespace GlobalTheory.CartanTensor

open Matrix
open scoped Kronecker ComplexOrder

variable {n d : ℕ}

theorem map_star_mul {a b c : Type} [Fintype b] (A : Matrix a b ℂ) (B : Matrix b c ℂ) : (A * B).map star = A.map star * B.map star := by
  ext i j; simp [mul_apply, star_sum]

theorem cartan_comm {M θ : Matrix (Fin n) (Fin n) ℂ} (h : IsCartan M θ) : M * θ.map star = θᵀ * M := by
  obtain ⟨h1, h2, -⟩ := h
  have h1' : θ.map star * θ.map star = 1 := by
    rw [← map_star_mul, h1]; ext i j; simp [one_apply]
  calc M * θ.map star = θᵀ * M * θ.map star * θ.map star := by rw [h2]
    _ = θᵀ * M := by rw [Matrix.mul_assoc (θᵀ * M), h1', Matrix.mul_one]

theorem cartan_posDef {M θ : Matrix (Fin n) (Fin n) ℂ} (hM : ∀ i j, star (M j i) = M i j) (h : IsCartan M θ) :
    (θᵀ * M).PosDef := by
  have hH : (θᵀ * M).IsHermitian := by
    rw [IsHermitian, conjTranspose_mul, ← cartan_comm h]
    congr 1 <;> ext i j <;> simp [hM]
  refine posDef_iff_dotProduct_mulVec.2 ⟨hH, fun c hc => Complex.pos_iff.2 ⟨?_, (hH.im_star_dotProduct_mulVec_self c).symm⟩⟩
  have hx : star c ≠ 0 := by simpa using hc
  have := h.2.2 (star c) hx
  rw [star_star] at this
  convert this using 2
  rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

end GlobalTheory.CartanTensor

namespace GlobalTheory.CartanTensor
open Matrix
open scoped Kronecker ComplexOrder
variable {n d : ℕ}

theorem quadruple_sum_eq_trace_transpose_mul (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin d) (Fin d) ℂ) (x y : Matrix (Fin n) (Fin d) ℂ) :
    (∑ i, ∑ j, ∑ k, ∑ l, x i j * A i k * B j l * star (y k l)) = trace (xᵀ * (A * y.map star * Bᵀ)) := by
  rw [← trace_transpose_mul, transpose_transpose]
  simp only [trace, diag_apply, mul_apply, transpose_apply, map_apply, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem quadruple_sum_eq_kronecker_quadraticForm (P : Matrix (Fin n) (Fin n) ℂ) (Q : Matrix (Fin d) (Fin d) ℂ) (x : Matrix (Fin n) (Fin d) ℂ) :
    (∑ i, ∑ j, ∑ k, ∑ l, x i j * P i k * Q j l * star (x k l)) =
      star (fun p : Fin n × Fin d => star (x p.1 p.2)) ⬝ᵥ ((P ⊗ₖ Q) *ᵥ fun p : Fin n × Fin d => star (x p.1 p.2)) := by
  simp only [dotProduct, mulVec, kronecker_apply, Fintype.sum_prod_type, Pi.star_apply, star_star, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

end GlobalTheory.CartanTensor

namespace GlobalTheory.CartanTensor
open Matrix
open scoped Kronecker ComplexOrder
variable {n d : ℕ}

theorem map_star_smulI {a b : Type} (M : Matrix a b ℂ) : (Complex.I • M).map star = (-Complex.I) • M.map star := by
  ext i j; simp

theorem cancelI {A B : Matrix (Fin d) (Fin d) ℂ} (h : Complex.I • A = Complex.I • B) : A = B :=
  smul_right_injective _ Complex.I_ne_zero h

theorem tensor_cartan_invariant_pos : ∀ (n d : ℕ) (JX θX : Matrix (Fin n) (Fin n) ℂ) (JW θW : Matrix (Fin d) (Fin d) ℂ),
    (∀ i j, star (JX j i) = JX i j) → IsCartan JX θX → (∀ i j, star (JW j i) = -JW i j) → IsCartan (Complex.I • JW) θW →
    ∀ x y : Matrix (Fin n) (Fin d) ℂ,
      (∑ i, ∑ j, ∑ k, ∑ l, (Complex.I • (θX * x * θWᵀ)) i j * JX i k * JW j l * star ((Complex.I • (θX * y * θWᵀ)) k l)) =
        (∑ i, ∑ j, ∑ k, ∑ l, x i j * JX i k * JW j l * star (y k l)) ∧
      (x ≠ 0 → 0 < -(∑ i, ∑ j, ∑ k, ∑ l, x i j * JX i k * JW j l * star ((Complex.I • (θX * x * θWᵀ)) k l)).re) := by
  intro n d JX θX JW θW hJX hX hJW hW x y
  have hWc : θWᵀ * JW * θW.map star = JW := by
    have h := hW.2.1
    rw [Matrix.mul_smul, Matrix.smul_mul] at h
    exact cancelI h
  have cW : JW * θW.map star = θWᵀ * JW := by
    have h := cartan_comm hW
    rw [Matrix.mul_smul, Matrix.smul_mul] at h
    exact cancelI h
  have cX := cartan_comm hX
  have hIW : ∀ i j, star ((Complex.I • JW) j i) = (Complex.I • JW) i j := by
    intro i j; simp [hJW]
  constructor
  · rw [quadruple_sum_eq_trace_transpose_mul, quadruple_sum_eq_trace_transpose_mul]
    have e1 : (Complex.I • (θX * x * θWᵀ))ᵀ * (JX * (Complex.I • (θX * y * θWᵀ)).map star * JWᵀ) =
        θW * (xᵀ * (θXᵀ * JX * θX.map star) * y.map star * (θW.map star)ᵀ * JWᵀ) := by
      rw [map_star_smulI, transpose_smul, map_star_mul, map_star_mul, transpose_mul, transpose_mul, transpose_transpose,
        transpose_map]
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc, mul_neg, Complex.I_mul_I, neg_neg, one_smul, neg_mul]
    have e2 : xᵀ * (θXᵀ * JX * θX.map star) * y.map star * (θW.map star)ᵀ * JWᵀ * θW =
        xᵀ * (θXᵀ * JX * θX.map star) * y.map star * (θWᵀ * JW * θW.map star)ᵀ := by
      simp only [transpose_mul, transpose_transpose, Matrix.mul_assoc]
    rw [e1, trace_mul_comm, e2, hX.2.1, hWc]
    simp only [Matrix.mul_assoc]
  · intro hx
    have e3 : xᵀ * (JX * (Complex.I • (θX * x * θWᵀ)).map star * JWᵀ) =
        -(xᵀ * ((θXᵀ * JX) * x.map star * (θWᵀ * (Complex.I • JW))ᵀ)) := by
      have h3 : xᵀ * (JX * (Complex.I • (θX * x * θWᵀ)).map star * JWᵀ) =
          (-Complex.I) • (xᵀ * (JX * θX.map star) * x.map star * (JW * θW.map star)ᵀ) := by
        rw [map_star_smulI, map_star_mul, map_star_mul, transpose_map, transpose_mul]
        simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
      rw [h3, cX, cW]
      simp only [Matrix.smul_mul, Matrix.mul_smul, transpose_smul, neg_smul, Matrix.mul_assoc]
    rw [quadruple_sum_eq_trace_transpose_mul, e3, trace_neg, Complex.neg_re, neg_neg,
      ← quadruple_sum_eq_trace_transpose_mul (θXᵀ * JX) (θWᵀ * (Complex.I • JW)) x x, quadruple_sum_eq_kronecker_quadraticForm]
    have hK := (cartan_posDef hJX hX).kronecker (cartan_posDef hIW hW)
    have hc : (fun p : Fin n × Fin d => star (x p.1 p.2)) ≠ 0 := by
      intro h; apply hx; ext i j; have := congrFun h (i, j); simpa using this
    exact (Complex.pos_iff.1 ((posDef_iff_dotProduct_mulVec.1 hK).2 hc)).1

end GlobalTheory.CartanTensor
end

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorCartanInvolution_invariant_and_positive : ∀ (n d : ℕ) (JX θX : Matrix (Fin n) (Fin n) ℂ) (JW θW : Matrix (Fin d) (Fin d) ℂ),
    (∀ i j, star (JX j i) = JX i j) → IsCartan JX θX → (∀ i j, star (JW j i) = -JW i j) → IsCartan (Complex.I • JW) θW →
    ∀ x y : Matrix (Fin n) (Fin d) ℂ,
      (∑ i, ∑ j, ∑ k, ∑ l, (Complex.I • (θX * x * θWᵀ)) i j * JX i k * JW j l * star ((Complex.I • (θX * y * θWᵀ)) k l)) =
        (∑ i, ∑ j, ∑ k, ∑ l, x i j * JX i k * JW j l * star (y k l)) ∧
      (x ≠ 0 → 0 < -(∑ i, ∑ j, ∑ k, ∑ l, x i j * JX i k * JW j l * star ((Complex.I • (θX * x * θWᵀ)) k l)).re) := by
  atlas_forward_decl GlobalTheory.CartanTensor.tensor_cartan_invariant_pos
end

section
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

noncomputable section

namespace GlobalTheory.GaussFockPair

open GlobalTheory.GaussFockJ

def tensC {n d : ℕ} (JX : Matrix (Fin n) (Fin n) ℂ) (JW : Matrix (Fin d) (Fin d) ℂ) (x y : Matrix (Fin n) (Fin d) ℂ) : ℂ :=
  ∑ i, ∑ j, ∑ k, ∑ l, x i j * JX i k * JW j l * star (y k l)

theorem tensC_zero_left {n d : ℕ} (JX : Matrix (Fin n) (Fin n) ℂ) (JW : Matrix (Fin d) (Fin d) ℂ) (y : Matrix (Fin n) (Fin d) ℂ) :
    tensC JX JW 0 y = 0 := by
  simp [tensC]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem pair_Psi {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (u v : Matrix (Fin n) (Fin d) (AE F E)) :
    GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (Psi M u).1 (Psi M v).2 -
                 GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (Psi M v).1 (Psi M u).2 =
      Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
        (evI F (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) u v)) := by
  rw [M.co.form u v, ← evIHom_apply, map_sub, map_sub]
  simp only [GlobalTheory.GaussLine.pairInf_apply, Psi, EvAt0.PolD.arc, dotProduct, map_sum, map_mul, evIHom_apply]

theorem exists_pos_complex_structure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' →
    ∃ J₀ : ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) →ₗ[ℝ] ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)),
      (∀ w, J₀ (J₀ w) = -w) ∧ (∀ w w', (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (J₀ w).1 (J₀ w').2 - GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (J₀ w').1 (J₀ w).2) = (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (w).1 (w').2 - GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (w').1 (w).2)) ∧
      (∀ w, w ≠ 0 → 0 < (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (w).1 (J₀ w).2 - GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (J₀ w).1 (w).2)) ∧
      ∀ u u' : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u → At (evI F) u' →
        (∀ w, u'.map (piInf (B.emb w)) = Complex.I • (X.θ w * u.map (piInf (B.emb w)) * (W.θ w)ᵀ)) →
        ((fun i => evI F ((M.co.e u').1 i), fun i => evI F ((M.co.e u').2 i)) : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) = J₀ ((fun i => evI F ((M.co.e u).1 i), fun i => evI F ((M.co.e u).2 i)) : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP
  have hcm := hP.base.cm
  choose R hRat hRmap using fun u : Matrix (Fin n) (Fin d) (AE F E) =>
    exists_mat_at hcm B.emb (fun w => Complex.I • (X.θ w * u.map (piInf (B.emb w)) * (W.θ w)ᵀ))
  have hRadd : ∀ u v, R (u + v) = R u + R v := by
    intro u v
    refine eq_of_map_piInf hcm B.emb (hRat _) (fun c hc => by rw [smul_add, hRat u c hc, hRat v c hc, add_zero])
      fun w => ?_
    rw [hRmap, Matrix.map_add _ (map_add _), Matrix.map_add _ (map_add _), hRmap, hRmap]
    simp only [Matrix.map_add _ (map_add _), Matrix.mul_add, Matrix.add_mul, smul_add]
  have hRsmul : ∀ (c : AF F) u, R (c • u) = c • R u := by
    intro c u
    refine eq_of_map_piInf hcm B.emb (hRat _) (fun c' hc' => by rw [smul_comm, hRat u c' hc', smul_zero])
      fun w => ?_
    rw [hRmap, map_smul_piInf, map_smul_piInf, hRmap]
    simp only [ Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_comm]
  have hRR : ∀ u, At (evI F) u → R (R u) = -u := by
    intro u hu
    refine eq_of_map_piInf hcm B.emb (hRat _) (fun c hc => by rw [smul_neg, hu c hc, neg_zero]) fun w => ?_
    rw [hRmap, Matrix.map_neg _ (map_neg _), hRmap]
    have hV := (hP.herm.cartan w).1
    have hW := (hP.skew.cartan w).1
    have hWt : (W.θ w)ᵀ * (W.θ w)ᵀ = 1 := by rw [← Matrix.transpose_mul, hW, Matrix.transpose_one]
    rw [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Complex.I_mul_I, neg_one_smul]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hV, Matrix.one_mul, Matrix.mul_assoc, hWt, Matrix.mul_one]

  have hXh : ∀ w, ∀ i j, star (X.J.map (B.emb w).1 j i) = X.J.map (B.emb w).1 i j := by
    intro w i j
    rw [Matrix.map_apply, Matrix.map_apply, ← hcm.2.2.2, hP.herm.herm]
  have hWs : ∀ w, ∀ i j, star (W.J.map (B.emb w).1 j i) = -W.J.map (B.emb w).1 i j := by
    intro w i j
    rw [Matrix.map_apply, Matrix.map_apply, ← hcm.2.2.2, hP.skew.skew, map_neg]
  have hloc := fun w => GlobalTheory.T.tensorCartanInvolution_invariant_and_positive n d (X.J.map (B.emb w).1) (X.θ w) (W.J.map (B.emb w).1) (W.θ w) (hXh w)
    (hP.herm.cartan w) (hWs w) (hP.skew.cartan w)
  have key : ∀ a b : Matrix (Fin n) (Fin d) (AE F E),
      Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) a b)) =
        ∑ w, -2 * (tensC (X.J.map (B.emb w).1) (W.J.map (B.emb w).1) (a.map (piInf (B.emb w)))
          (b.map (piInf (B.emb w)))).re := by
    intro a b
    rw [GlobalTheory.ThK.EvAt0.PlaneQ.trace_symp_neg_one F E σ hcm B.emb n d X.J W.J a b]
    rfl
  have hinv : ∀ a b w, tensC (X.J.map (B.emb w).1) (W.J.map (B.emb w).1) ((R a).map (piInf (B.emb w)))
      ((R b).map (piInf (B.emb w))) = tensC (X.J.map (B.emb w).1) (W.J.map (B.emb w).1) (a.map (piInf (B.emb w)))
      (b.map (piInf (B.emb w))) := by
    intro a b w
    rw [hRmap, hRmap]
    exact (hloc w _ _).1
  have hpos : ∀ a w, a.map (piInf (B.emb w)) ≠ 0 → 0 < -(tensC (X.J.map (B.emb w).1) (W.J.map (B.emb w).1)
      (a.map (piInf (B.emb w))) ((R a).map (piInf (B.emb w)))).re := by
    intro a w ha
    rw [hRmap]
    exact (hloc w _ (a.map (piInf (B.emb w)))).2 ha
  let J : ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) →
      ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) :=
    fun w => Psi M (R (Phi M w))
  have hPsi_smul : ∀ (t : ℝ) v, At (evI F) v → Psi M (realAd F t • v) = t • Psi M v := by
    intro t v hv
    rw [← Phi_Psi M hv, ← Phi_smul, Psi_Phi, Psi_Phi]
  let J₀ : ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) →ₗ[ℝ]
      ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) :=
    { toFun := J
      map_add' := fun w w' => by
        show Psi M (R (Phi M (w + w'))) = Psi M (R (Phi M w)) + Psi M (R (Phi M w'))
        rw [Phi_add, hRadd, Psi_add]
      map_smul' := fun t w => by
        show Psi M (R (Phi M (t • w))) = t • Psi M (R (Phi M w))
        rw [Phi_smul, hRsmul, hPsi_smul t _ (hRat _)] }
  have hPsi0 : Psi M (0 : Matrix (Fin n) (Fin d) (AE F E)) = 0 := by
    have h := Psi_add M (0 : Matrix (Fin n) (Fin d) (AE F E)) 0
    rw [add_zero] at h
    exact add_left_cancel (h.symm.trans (add_zero _).symm)
  refine ⟨J₀, fun w => ?_, fun w w' => ?_, fun w hw => ?_, fun u u' hu hu' hmap => ?_⟩
  · show Psi M (R (Phi M (Psi M (R (Phi M w))))) = -w
    rw [Phi_Psi M (hRat _), hRR _ (at_Phi M w), Psi_neg, Psi_Phi]
  · show GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (Psi M (R (Phi M w))).1 (Psi M (R (Phi M w'))).2 -
        GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (Psi M (R (Phi M w'))).1 (Psi M (R (Phi M w))).2 = _
    conv_rhs => rw [← Psi_Phi M w, ← Psi_Phi M w']
    rw [pair_Psi, pair_Psi, key, key]
    exact Finset.sum_congr rfl fun v _ => by rw [hinv]
  · have hw' := Psi_Phi M w
    have hat := at_Phi M w
    show 0 < GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) w.1 (Psi M (R (Phi M w))).2 -
        GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (Psi M (R (Phi M w))).1 w.2
    generalize Phi M w = a at hw' hat ⊢
    subst hw'
    rw [pair_Psi, key]
    have hex : ∃ v, a.map (piInf (B.emb v)) ≠ 0 := by
      by_contra hn
      push_neg at hn
      have ha0 : a = 0 := eq_of_map_piInf hcm B.emb hat (fun c _ => smul_zero c)
        fun v => by rw [hn v, Matrix.map_zero _ (map_zero _)]
      exact hw (by rw [ha0, hPsi0])
    obtain ⟨v, hv⟩ := hex
    refine Finset.sum_pos' (fun v' _ => ?_) ⟨v, Finset.mem_univ _, by have := hpos a v hv; linarith⟩
    by_cases h0 : a.map (piInf (B.emb v')) = 0
    · rw [h0, tensC_zero_left, Complex.zero_re, mul_zero]
    · have := hpos a v' h0; linarith
  · change Psi M u' = Psi M (R (Phi M (Psi M u)))
    rw [Phi_Psi M hu]
    congr 1
    exact eq_of_map_piInf hcm B.emb hu' (hRat u) fun w => by rw [hmap, hRmap]

end GlobalTheory.GaussFockPair
end
end

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_positive_complex_structure_darboux_pair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' →
    ∃ J₀ : ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) →ₗ[ℝ] ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)),
      (∀ w, J₀ (J₀ w) = -w) ∧ (∀ w w', (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (J₀ w).1 (J₀ w').2 - GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (J₀ w').1 (J₀ w).2) = (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (w).1 (w').2 - GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (w').1 (w).2)) ∧
      (∀ w, w ≠ 0 → 0 < (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (w).1 (J₀ w).2 - GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) (J₀ w).1 (w).2)) ∧
      ∀ u u' : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u → At (evI F) u' →
        (∀ w, u'.map (piInf (B.emb w)) = Complex.I • (X.θ w * u.map (piInf (B.emb w)) * (W.θ w)ᵀ)) →
        ((fun i => evI F ((M.co.e u').1 i), fun i => evI F ((M.co.e u').2 i)) : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) = J₀ ((fun i => evI F ((M.co.e u).1 i), fun i => evI F ((M.co.e u).2 i)) : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) := by
  atlas_forward_decl GlobalTheory.GaussFockPair.exists_pos_complex_structure
end

section
section
open scoped Matrix

namespace GlobalTheory

theorem siegel_fock_exists : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (J : (V × V) →ₗ[ℝ] (V × V)), (∀ x y, β x y = β y x) → (∀ w, J (J w) = -w) →
    (∀ w w', β (J w).1 (J w').2 - β (J w').1 (J w).2 = β w.1 w'.2 - β w'.1 w.2) →
    (∀ w, w ≠ 0 → 0 < β w.1 (J w).2 - β (J w).1 w.2) →
    ∃ (Q : V →L[ℝ] V →L[ℝ] ℂ) (c : ℝ), 0 < c ∧ (∀ x, c * ‖x‖ ^ 2 ≤ (Q x x).re) ∧ (∀ x y, Q x y = Q y x) ∧
      ∀ w x, Q x (J w).1 + (Real.pi : ℂ) * Complex.I * (β x (J w).2 : ℂ) = Complex.I * (Q x w.1 + (Real.pi : ℂ) * Complex.I * (β x w.2 : ℂ)) := by
  intro V _ _ _ β J hsym hJJ hJ hpos
  set Φ : (V × V) →ₗ[ℝ] (V × V) :=
    LinearMap.inr ℝ V V ∘ₗ LinearMap.fst ℝ V V + J ∘ₗ LinearMap.inr ℝ V V ∘ₗ LinearMap.snd ℝ V V with hΦdef
  have hΦ : ∀ u : V × V, Φ u = (0, u.1) + J (0, u.2) := by
    intro u; simp [hΦdef]
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    rw [hΦ] at hu
    have h1 : (J (0, u.2)).1 = 0 := by
      have := congrArg Prod.fst hu; simpa using this
    have hb : u.2 = 0 := by
      by_contra hne
      have := hpos (0, u.2) (by simpa using hne)
      simp [h1] at this
    have hJ0 : J (0, 0) = 0 := J.map_zero
    have ha : u.1 = 0 := by
      have := congrArg Prod.snd hu; simpa [hb, hJ0] using this
    exact Prod.ext ha hb
  set E := LinearEquiv.ofInjectiveEndo Φ hinj with hEdef
  have hE : ∀ w, Φ (E.symm w) = w := fun w => by
    show E (E.symm w) = w
    exact E.apply_symm_apply w
  have hJ0 : J (0, 0) = 0 := J.map_zero
  set A : V →ₗ[ℝ] V := LinearMap.fst ℝ V V ∘ₗ E.symm.toLinearMap ∘ₗ LinearMap.inl ℝ V V with hAdef
  set B : V →ₗ[ℝ] V := LinearMap.snd ℝ V V ∘ₗ E.symm.toLinearMap ∘ₗ LinearMap.inl ℝ V V with hBdef
  have hAB : ∀ p, E.symm (p, 0) = (A p, B p) := fun p => by simp [hAdef, hBdef]
  have hP0 : ∀ q, E.symm (0, q) = (q, 0) := fun q => by
    apply E.injective
    rw [E.apply_symm_apply]
    show (0, q) = Φ (q, 0)
    rw [hΦ]; simp [hJ0]
  have hsplit : ∀ w : V × V, E.symm w = (A w.1 + w.2, B w.1) := fun w => by
    have hw : w = (w.1, 0) + (0, w.2) := by simp
    rw [hw, map_add, hAB, hP0]; simp
  have hJB : ∀ p, J (0, B p) = (p, -A p) := fun p => by
    have := hE (p, 0)
    rw [hAB, hΦ] at this
    have h2 : J (0, B p) = (p, 0) - (0, A p) := by rw [← this]; abel
    rw [h2]; simp
  have hPJ : ∀ w : V × V, E.symm (J w) = (-(E.symm w).2, (E.symm w).1) := fun w => by
    apply E.injective
    rw [E.apply_symm_apply]
    show J w = Φ _
    conv_lhs => rw [← hE w]
    rw [hΦ, hΦ, map_add, hJJ]
    ext <;> simp <;> abel
  have hAsym : ∀ x y, β x (A y) = β y (A x) := fun x y => by
    have := hJ (0, B x) (0, B y)
    rw [hJB, hJB] at this
    simp at this
    linarith
  have hBsym : ∀ x y, β x (B y) = β y (B x) := fun x y => by
    have := hJ (J (0, B x)) (0, B y)
    rw [hJJ, hJB, hJB] at this
    simp at this
    linarith
  have hBpos : ∀ x, x ≠ 0 → 0 < -β x (B x) := fun x hx => by
    have hne : ((0 : V), B x) ≠ 0 := by
      intro h0
      have h1 : J (0, B x) = 0 := by rw [h0]; exact J.map_zero
      rw [hJB] at h1
      exact hx (congrArg Prod.fst h1)
    have := hpos (0, B x) hne
    rw [hJB] at this
    simpa using this
  let Q' : V →ₗ[ℝ] V →ₗ[ℝ] ℂ := LinearMap.mk₂ ℝ
    (fun x y => ((Real.pi * β x (A y) : ℝ) : ℂ) * Complex.I - ((Real.pi * β x (B y) : ℝ) : ℂ))
    (fun m₁ m₂ n => by simp; ring)
    (fun c m n => by simp; ring)
    (fun m n₁ n₂ => by simp; ring)
    (fun c m n => by simp; ring)
  let Q : V →L[ℝ] V →L[ℝ] ℂ := LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (V →ₗ[ℝ] ℂ) ≃ₗ[ℝ] (V →L[ℝ] ℂ)).toLinearMap ∘ₗ Q')
  have hQ : ∀ x y, Q x y = ((Real.pi * β x (A y) : ℝ) : ℂ) * Complex.I - ((Real.pi * β x (B y) : ℝ) : ℂ) :=
    fun x y => rfl
  have hre : ∀ x, (Q x x).re = Real.pi * -β x (B x) := fun x => by
    rw [hQ]; simp
  have hscale : ∀ (t : ℝ) (y : V), Real.pi * -β (t • y) (B (t • y)) = t ^ 2 * (Real.pi * -β y (B y)) :=
    fun t y => by simp; ring
  have hcont : Continuous fun x => (Q x x).re := by fun_prop
  have hsym' : ∀ x y, Q x y = Q y x := fun x y => by rw [hQ, hQ, hAsym x y, hBsym x y]
  have hfock : ∀ w x, Q x (J w).1 + (Real.pi : ℂ) * Complex.I * (β x (J w).2 : ℂ) =
      Complex.I * (Q x w.1 + (Real.pi : ℂ) * Complex.I * (β x w.2 : ℂ)) := fun w x => by
    have e1 := hsplit (J w)
    rw [hPJ, hsplit w] at e1
    have h1 : A (J w).1 + (J w).2 = -(B w.1) := (congrArg Prod.fst e1).symm
    have h2 : B (J w).1 = A w.1 + w.2 := (congrArg Prod.snd e1).symm
    have hb1 : β x (A (J w).1) = -β x (B w.1) - β x (J w).2 := by
      have := congrArg (β x) h1; simp at this; linarith
    have hb2 : β x (B (J w).1) = β x (A w.1) + β x w.2 := by rw [h2]; simp
    rw [hQ, hQ, hb1, hb2]
    push_cast
    linear_combination (-((Real.pi : ℂ) * (β x (A w.1) : ℂ) + (Real.pi : ℂ) * (β x w.2 : ℂ))) * Complex.I_sq
  by_cases hs : (Metric.sphere (0 : V) 1).Nonempty
  · obtain ⟨u, hu, hmin⟩ := (isCompact_sphere (0 : V) 1).exists_isMinOn hs hcont.continuousOn
    have hu0 : u ≠ 0 := by
      intro h; rw [h] at hu; simp at hu
    refine ⟨Q, (Q u u).re, ?_, ?_, hsym', hfock⟩
    · rw [hre]; exact mul_pos Real.pi_pos (hBpos u hu0)
    · intro x
      by_cases hx : x = 0
      · subst hx; simp
      · have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
        have hu' : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : V) 1 := by
          rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
        have hm : (Q u u).re ≤ (Q (‖x‖⁻¹ • x) (‖x‖⁻¹ • x)).re := hmin hu'
        have key : Real.pi * -β x (B x) = ‖x‖ ^ 2 * (Real.pi * -β (‖x‖⁻¹ • x) (B (‖x‖⁻¹ • x))) := by
          rw [hscale]; field_simp
        rw [hre, hre] at hm
        rw [hre u, hre x, key]
        have := mul_le_mul_of_nonneg_left hm (sq_nonneg ‖x‖)
        linarith
  · refine ⟨Q, 1, one_pos, ?_, hsym', hfock⟩
    intro x
    by_cases hx : x = 0
    · subst hx; simp
    · exfalso
      apply hs
      refine ⟨‖x‖⁻¹ • x, ?_⟩
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_pos_iff.mpr hx).ne']

end GlobalTheory
end

open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_siegel_fock_form_of_complex_structure : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (J : (V × V) →ₗ[ℝ] (V × V)), (∀ x y, β x y = β y x) → (∀ w, J (J w) = -w) →
    (∀ w w', β (J w).1 (J w').2 - β (J w').1 (J w).2 = β w.1 w'.2 - β w'.1 w.2) →
    (∀ w, w ≠ 0 → 0 < β w.1 (J w).2 - β (J w).1 w.2) →
    ∃ (Q : V →L[ℝ] V →L[ℝ] ℂ) (c : ℝ), 0 < c ∧ (∀ x, c * ‖x‖ ^ 2 ≤ (Q x x).re) ∧ (∀ x y, Q x y = Q y x) ∧
      ∀ w x, Q x (J w).1 + (Real.pi : ℂ) * Complex.I * (β x (J w).2 : ℂ) = Complex.I * (Q x w.1 + (Real.pi : ℂ) * Complex.I * (β x w.2 : ℂ)) := by
  atlas_forward_decl GlobalTheory.siegel_fock_exists
end

section
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_schwartz_eq_cexp_neg_form : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (Q : V →L[ℝ] V →L[ℝ] ℂ) (c : ℝ),
    0 < c → (∀ x, c * ‖x‖ ^ 2 ≤ (Q x x).re) →
    ∃ g : SchwartzMap V ℂ, (∀ x, g x = Complex.exp (-(Q x x))) ∧ ∀ x p, fderiv ℝ (⇑g) x p = -(Q x p + Q p x) * g x := by
  first | exact @GlobalTheory.GaussComplexForm.exists_schwartz_cexp_neg_form | exact GlobalTheory.GaussComplexForm.exists_schwartz_cexp_neg_form | (intros; apply GlobalTheory.GaussComplexForm.exists_schwartz_cexp_neg_form <;> assumption)
end

section
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

noncomputable section
namespace GlobalTheory.GaussVacPair
open GlobalTheory.GaussFockJ GlobalTheory.ThK.EvAt0.PolD

theorem actsD_unique {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    {T : ℝ → ((κ → AF F) → ℂ) → (κ → AF F) → ℂ} {f f₁ f₂ : SInf F κ}
    (h1 : ActsD (evI F) T f f₁) (h2 : ActsD (evI F) T f f₂) : f₁ = f₂ := by
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.ArchRest.exists_rest_arch (F := F) κ
  ext y
  have hr := hR f
  let x : κ → AF F := fun i => liftA (y i)
  have hx : At (evI F) x := fun c hc => funext fun i => smul_liftA hc (y i)
  have e := (h1 R hr x).unique (h2 R hr x)
  have hRx : R x = R 0 := by
    have := hr.1 0 x hx
    rwa [zero_add] at this
  have hl : (fun i => evI F (x i)) = y := funext fun i => evI_liftA (y i)
  simp only [tens, hl, hRx] at e
  exact mul_right_cancel₀ hR0 e

theorem exists_gauss_vacuum : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∃ g : SInf F (Fin n × Fin d), M.IsGauss B.ψ B.emb g ∧
      ∃ (Q : (Fin n × Fin d → mixedEmbedding.mixedSpace F) →L[ℝ] (Fin n × Fin d → mixedEmbedding.mixedSpace F) →L[ℝ] ℂ) (c : ℝ),
        0 < c ∧ (∀ x, c * ‖x‖ ^ 2 ≤ (Q x x).re) ∧ ∀ x, g x = Complex.exp (-(Q x x)) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP
  have hψ : IsStd B.ψ := hP.base.std
  obtain ⟨J₀, hJJ, hJω, hJpos, hJrel⟩ := GlobalTheory.T.exists_positive_complex_structure_darboux_pair F E σ B n d X W M χX χW om r s r' s' hP
  have hsym : ∀ x y : (Fin n × Fin d → mixedEmbedding.mixedSpace F), GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) x y = GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) y x := by
    intro x y
    simp only [GlobalTheory.GaussLine.pairInf_apply, mul_comm]
  obtain ⟨Q, c, hc, hQc, hQs, hQJ⟩ := GlobalTheory.T.exists_siegel_fock_form_of_complex_structure (Fin n × Fin d → mixedEmbedding.mixedSpace F) (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d)) J₀ hsym hJJ hJω hJpos
  obtain ⟨g, hg, hgd⟩ := GlobalTheory.T.exists_schwartz_eq_cexp_neg_form (Fin n × Fin d → mixedEmbedding.mixedSpace F) Q c hc hQc
  refine ⟨g, ⟨fun _ => 1, ?_⟩, Q, c, hc, hQc, hg⟩
  intro u u' hu hu' hrel f f' hf hf'
  have hrel' : ∀ w, u'.map (piInf (B.emb w)) = Complex.I • (X.θ w * u.map (piInf (B.emb w)) * (W.θ w)ᵀ) := by
    intro w
    rw [hrel w]
    simp
  have key : ∀ v : Matrix (Fin n) (Fin d) (AE F E), At (evI F) v → ∀ h : SInf F (Fin n × Fin d),
      ActsD (evI F) (M.heisLine B.ψ v) g h → ∀ x, h x = GlobalTheory.GaussLine.dHeis (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d)) (Psi M v) g x := by
    intro v hv h hh x
    have h0 := actsD_Phi hψ M (Psi M v) g
    rw [Phi_Psi M hv] at h0
    rw [actsD_unique hh h0, dHeis_eq_dOp]
  have hJ : Psi M u' = J₀ (Psi M u) := hJrel u u' hu hu' hrel'
  have hd : ∀ (w : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) x, GlobalTheory.GaussLine.dHeis (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d)) w g x =
      -2 * (Q x w.1 + (Real.pi : ℂ) * Complex.I * (GlobalTheory.GaussLine.pairInf F (Fin n × Fin d) x w.2 : ℂ)) * g x := by
    intro w x
    rw [GlobalTheory.GaussLine.dHeis, hgd x w.1, hQs w.1 x]
    ring
  ext x
  rw [SchwartzMap.smul_apply, key u' hu' f' hf' x, key u hu f hf x, hJ, hd, hd, hQJ, smul_eq_mul]
  ring

end GlobalTheory.GaussVacPair
end
end

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_gaussVacuum_nondegenerate_gaussian_dualPair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∃ g : SInf F (Fin n × Fin d), M.IsGauss B.ψ B.emb g ∧
      ∃ (Q : (Fin n × Fin d → mixedEmbedding.mixedSpace F) →L[ℝ] (Fin n × Fin d → mixedEmbedding.mixedSpace F) →L[ℝ] ℂ) (c : ℝ),
        0 < c ∧ (∀ x, c * ‖x‖ ^ 2 ≤ (Q x x).re) ∧ ∀ x, g x = Complex.exp (-(Q x x)) := by
  atlas_forward_decl GlobalTheory.GaussVacPair.exists_gauss_vacuum
end

section
section
open FourierTransform MeasureTheory Filter Topology

namespace GlobalTheory

theorem exists_equiv_euclidean_pi_mul_norm_sq_eq_re (V : Type) [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] (Q : V →L[ℝ] V →L[ℝ] ℂ) (c : ℝ)
    (hc : 0 < c) (hQ : ∀ x, c * ‖x‖ ^ 2 ≤ (Q x x).re) :
    ∃ A : V ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V)),
      ∀ x, Real.pi * ‖A x‖ ^ 2 = (Q x x).re := by
  classical
  let B : LinearMap.BilinForm ℝ V := LinearMap.mk₂ ℝ (fun x y => (Q x y).re)
    (by intros; simp) (by intros; simp) (by intros; simp) (by intros; simp)
  let q : QuadraticForm ℝ V := B.toQuadraticMap
  have hq : ∀ x, q x = (Q x x).re := fun x => rfl
  obtain ⟨w, ⟨e⟩⟩ := QuadraticForm.equivalent_weightedSumSquares q
  have he : ∀ x, ∑ i, w i * (e x i * e x i) = (Q x x).re := by
    intro x
    have := e.map_app x
    rw [QuadraticMap.weightedSumSquares_apply] at this
    simpa [hq] using this
  have hw : ∀ i, 0 < w i := by
    intro i
    have h1 := he (e.symm (Pi.single i 1))
    have h2 : e (e.symm (Pi.single i 1)) = Pi.single i 1 := e.toLinearEquiv.apply_symm_apply _
    have hne : e.symm (Pi.single i 1) ≠ 0 := by
      intro h
      rw [h, map_zero] at h2
      have := congrFun h2 i
      simp at this
    rw [h2, Finset.sum_eq_single i (by intro j _ hj; simp [hj]) (by simp)] at h1
    have h3 := hQ (e.symm (Pi.single i 1))
    have h4 : 0 < c * ‖e.symm (Pi.single i 1)‖ ^ 2 := by
      have := norm_pos_iff.mpr hne
      positivity
    simp at h1
    linarith
  have hs : ∀ i, Real.sqrt (w i / Real.pi) ≠ 0 := fun i =>
    (Real.sqrt_pos.mpr (div_pos (hw i) Real.pi_pos)).ne'
  let D : (Fin (Module.finrank ℝ V) → ℝ) ≃ₗ[ℝ] (Fin (Module.finrank ℝ V) → ℝ) :=
    LinearEquiv.piCongrRight fun i =>
      LinearEquiv.smulOfNeZero ℝ ℝ (Real.sqrt (w i / Real.pi)) (hs i)
  let A : V ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) :=
    (e.toLinearEquiv.trans D).trans (WithLp.linearEquiv 2 ℝ _).symm
  have hA : ∀ x i, A x i = Real.sqrt (w i / Real.pi) * e x i := fun x i => rfl
  refine ⟨A.toContinuousLinearEquiv, fun x => ?_⟩
  rw [← he, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (A.toContinuousLinearEquiv x) i = Real.sqrt (w i / Real.pi) * e x i := hA x i
  rw [this, Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt (div_pos (hw i) Real.pi_pos).le]
  have := Real.pi_pos.ne'
  field_simp

end GlobalTheory
end

open FourierTransform MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_euclidean_equiv_pi_mul_norm_sq_eq_re : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (Q : V →L[ℝ] V →L[ℝ] ℂ) (c : ℝ),
    0 < c → (∀ x, c * ‖x‖ ^ 2 ≤ (Q x x).re) →
    ∃ A : V ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V)), ∀ x, Real.pi * ‖A x‖ ^ 2 = (Q x x).re := by
  atlas_forward_decl GlobalTheory.exists_equiv_euclidean_pi_mul_norm_sq_eq_re
end

section
section
open FourierTransform MeasureTheory Filter Topology

namespace GlobalTheory.GaussTransport

theorem iteratedDeriv_cexp_mul (a : ℂ) (n : ℕ) :
    iteratedDeriv n (fun y : ℝ => Complex.exp (a * y)) = fun y : ℝ => a ^ n * Complex.exp (a * y) := by
  induction n with
  | zero => funext y; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext y
    have h1 : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 y := by
      simpa using (hasDerivAt_id y).ofReal_comp
    have h : HasDerivAt (fun y : ℝ => a ^ n * Complex.exp (a * y)) (a ^ n * (Complex.exp (a * y) * (a * 1))) y :=
      ((h1.const_mul a).cexp).const_mul (a ^ n)
    rw [h.deriv]; ring

theorem hasTemperateGrowth_expI : Function.HasTemperateGrowth (fun t : ℝ => Complex.exp (Complex.I * t)) := by
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => Complex.exp (Complex.I * y)) :=
    (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp
  refine ⟨hc, fun n => ⟨0, ‖Complex.I‖ ^ n, fun x => ?_⟩⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_cexp_mul, pow_zero, mul_one, norm_mul, norm_pow]
  have h1 : ‖Complex.exp (Complex.I * x)‖ = 1 := by
    rw [mul_comm, Complex.norm_exp_ofReal_mul_I]
  rw [h1, mul_one]

theorem hasTemperateGrowth_chirp {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Q : V →L[ℝ] V →L[ℝ] ℂ) (s : ℝ) :
    Function.HasTemperateGrowth (fun x : V => Complex.exp (Complex.I * ((s * (Q x x).im : ℝ) : ℂ))) := by
  have h1 : Function.HasTemperateGrowth (fun x : V => Q x x) :=
    Q.bilinear_hasTemperateGrowth Function.HasTemperateGrowth.id' Function.HasTemperateGrowth.id'
  have h2 : Function.HasTemperateGrowth (fun x : V => s * (Q x x).im) := by
    have := ((s • Complex.imCLM : ℂ →L[ℝ] ℝ)).hasTemperateGrowth.comp h1
    simpa [Function.comp_def] using this
  exact hasTemperateGrowth_expI.comp h2

end GlobalTheory.GaussTransport

namespace GlobalTheory.GaussTransport

open LineDeriv in

theorem transport : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (A : V ≃L[ℝ] E) (Q : V →L[ℝ] V →L[ℝ] ℂ) (N : Submodule ℂ (SchwartzMap V ℂ)),
    (∀ x, Real.pi * ‖A x‖ ^ 2 = (Q x x).re) →
    (∀ (v : V) (f f₁ : SchwartzMap V ℂ), f ∈ N → (∀ x, f₁ x = fderiv ℝ (⇑f) x v) → f₁ ∈ N) →
    (∀ (ℓ : V →L[ℝ] ℝ) (f f₁ : SchwartzMap V ℂ), f ∈ N → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ N) →
    ∃ N₂ : Submodule ℂ (SchwartzMap E ℂ),
      (∀ (v : E) (f f₁ : SchwartzMap E ℂ), f ∈ N₂ → (∀ x, f₁ x = fderiv ℝ (⇑f) x v) → f₁ ∈ N₂) ∧
      (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ N₂ → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ N₂) ∧
      (∀ (g : SchwartzMap V ℂ) (G : SchwartzMap E ℂ), (∀ x, g x = Complex.exp (-(Q x x))) → g ∈ N →
        (∀ y, G y = Complex.exp (-((Real.pi * ‖y‖ ^ 2 : ℝ) : ℂ))) → G ∈ N₂) ∧
      (Dense (N₂ : Set (SchwartzMap E ℂ)) → Dense (N : Set (SchwartzMap V ℂ))) := by
  intro V _ _ _ E _ _ _ A Q N hQ hD hL
  set χ : V → ℂ := fun x => Complex.exp (Complex.I * ((-1 * (Q x x).im : ℝ) : ℂ)) with hχdef
  set χi : V → ℂ := fun x => Complex.exp (Complex.I * ((1 * (Q x x).im : ℝ) : ℂ)) with hχidef
  have hχ : χ.HasTemperateGrowth := hasTemperateGrowth_chirp Q (-1)
  have hχi : χi.HasTemperateGrowth := hasTemperateGrowth_chirp Q 1
  have hχχi : ∀ x, χ x * χi x = 1 := by
    intro x
    simp only [hχdef, hχidef, ← Complex.exp_add]
    rw [← Complex.exp_zero]; congr 1; push_cast; ring
  let Ψ : SchwartzMap E ℂ →L[ℂ] SchwartzMap V ℂ :=
    (SchwartzMap.smulLeftCLM ℂ χ).comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A)
  have hΨ : ∀ f x, Ψ f x = χ x * f (A x) := by
    intro f x
    simp [Ψ, SchwartzMap.smulLeftCLM_apply_apply hχ]
  refine ⟨N.comap (Ψ : SchwartzMap E ℂ →ₗ[ℂ] SchwartzMap V ℂ), ?_, ?_, ?_, ?_⟩
  · intro w f f₁ hf hf₁
    rw [Submodule.mem_comap] at hf ⊢
    simp only [ContinuousLinearMap.coe_coe] at hf ⊢
    set v : V := A.symm w with hv
    let lam : V →L[ℝ] ℝ := Complex.imCLM.comp (Q.flip v + Q v)
    have hlam : ∀ x, lam x = (Q x v).im + (Q v x).im := by intro x; simp [lam]
    have hlamT : (fun x : V => ((lam x : ℝ) : ℂ)).HasTemperateGrowth :=
      (Complex.ofRealCLM.comp lam).hasTemperateGrowth
    have h1N : ∂_{v} (Ψ f) ∈ N := hD v (Ψ f) _ hf (fun x => SchwartzMap.lineDerivOp_apply_eq_fderiv v (Ψ f) x)
    have h2N : SchwartzMap.smulLeftCLM ℂ (fun x : V => ((lam x : ℝ) : ℂ)) (Ψ f) ∈ N :=
      hL lam (Ψ f) _ hf (fun x => by rw [SchwartzMap.smulLeftCLM_apply_apply hlamT, smul_eq_mul])
    have hder : ∀ x, fderiv ℝ (⇑(Ψ f)) x v =
        χ x * fderiv ℝ (⇑f) (A x) w - Complex.I * ((lam x : ℂ) * (χ x * f (A x))) := by
      intro x
      have hfun : (⇑(Ψ f)) = χ * (fun y => f (A y)) := funext (hΨ f)
      let L : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp ((-1 : ℝ) • Complex.imCLM)
      have hq := Q.hasFDerivAt_of_bilinear (hasFDerivAt_id x) (hasFDerivAt_id x)
      have hu := ((L.hasFDerivAt).comp x hq).const_mul Complex.I
      have hχd : HasFDerivAt χ (Complex.exp (Complex.I * L (Q x x)) • (Complex.I • (L.comp
          (((ContinuousLinearMap.precompR V Q) (id x)) (ContinuousLinearMap.id ℝ V) +
            ((ContinuousLinearMap.precompL V Q) (ContinuousLinearMap.id ℝ V)) (id x))))) x := by
        refine hu.cexp.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
        simp [χ, L]
      have hfA : HasFDerivAt (fun y => f (A y)) ((fderiv ℝ (⇑f) (A x)).comp (A : V →L[ℝ] E)) x :=
        (f.differentiableAt.hasFDerivAt).comp x A.hasFDerivAt
      rw [hfun, (hχd.mul hfA).fderiv]
      have hχx : χ x = Complex.exp (-(Complex.I * ((Q x x).im : ℂ))) := by simp [χ]
      simp [L, v, hlam]
      rw [hχx]
      ring
    have hsum : Ψ f₁ = ∂_{v} (Ψ f) + Complex.I • SchwartzMap.smulLeftCLM ℂ (fun x : V => ((lam x : ℝ) : ℂ)) (Ψ f) := by
      ext x
      rw [SchwartzMap.add_apply, SchwartzMap.smul_apply, SchwartzMap.smulLeftCLM_apply_apply hlamT,
        SchwartzMap.lineDerivOp_apply_eq_fderiv, hder, hΨ, hΨ, hf₁, smul_eq_mul, smul_eq_mul]
      ring
    rw [hsum]
    exact N.add_mem h1N (N.smul_mem _ h2N)
  · intro ℓ f f₁ hf hf₁
    rw [Submodule.mem_comap] at hf ⊢
    simp only [ContinuousLinearMap.coe_coe] at hf ⊢
    refine hL (ℓ.comp (A : V →L[ℝ] E)) (Ψ f) (Ψ f₁) hf (fun x => ?_)
    rw [hΨ, hΨ, hf₁]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
    ring
  · intro g G hg hgN hG
    rw [Submodule.mem_comap]
    simp only [ContinuousLinearMap.coe_coe]
    have hΨG : Ψ G = g := by
      ext x
      rw [hΨ, hG, hg, hχdef]
      simp only
      rw [← Complex.exp_add]
      congr 1
      conv_rhs => rw [← Complex.re_add_im (Q x x)]
      rw [← hQ x]
      push_cast
      ring
    rw [hΨG]; exact hgN
  · intro hd
    have hsurj : Function.Surjective Ψ := by
      intro k
      refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.symm (SchwartzMap.smulLeftCLM ℂ χi k), ?_⟩
      ext x
      rw [hΨ]
      simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
        ContinuousLinearEquiv.symm_apply_apply, SchwartzMap.smulLeftCLM_apply_apply hχi, smul_eq_mul]
      rw [← mul_assoc, hχχi, one_mul]
    refine (hsurj.denseRange.dense_image Ψ.continuous hd).mono ?_
    rintro _ ⟨f, hf, rfl⟩
    exact hf

end GlobalTheory.GaussTransport
end

open FourierTransform MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_density_transport_linearEquiv_chirp : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (A : V ≃L[ℝ] E) (Q : V →L[ℝ] V →L[ℝ] ℂ) (N : Submodule ℂ (SchwartzMap V ℂ)),
    (∀ x, Real.pi * ‖A x‖ ^ 2 = (Q x x).re) →
    (∀ (v : V) (f f₁ : SchwartzMap V ℂ), f ∈ N → (∀ x, f₁ x = fderiv ℝ (⇑f) x v) → f₁ ∈ N) →
    (∀ (ℓ : V →L[ℝ] ℝ) (f f₁ : SchwartzMap V ℂ), f ∈ N → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ N) →
    ∃ N₂ : Submodule ℂ (SchwartzMap E ℂ),
      (∀ (v : E) (f f₁ : SchwartzMap E ℂ), f ∈ N₂ → (∀ x, f₁ x = fderiv ℝ (⇑f) x v) → f₁ ∈ N₂) ∧
      (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ N₂ → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ N₂) ∧
      (∀ (g : SchwartzMap V ℂ) (G : SchwartzMap E ℂ), (∀ x, g x = Complex.exp (-(Q x x))) → g ∈ N →
        (∀ y, G y = Complex.exp (-((Real.pi * ‖y‖ ^ 2 : ℝ) : ℂ))) → G ∈ N₂) ∧
      (Dense (N₂ : Set (SchwartzMap E ℂ)) → Dense (N : Set (SchwartzMap V ℂ))) := by
  atlas_forward_decl GlobalTheory.GaussTransport.transport
end

section
section
open FourierTransform MeasureTheory Filter Topology

namespace GlobalTheory

theorem exists_fourier_stable_gaussian_submodule :
    ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (N : Submodule ℂ (SchwartzMap E ℂ)) (G : SchwartzMap E ℂ),
    (∀ y, G y = Complex.exp (-((Real.pi * ‖y‖ ^ 2 : ℝ) : ℂ))) → G ∈ N →
    (∀ (v : E) (f f₁ : SchwartzMap E ℂ), f ∈ N → (∀ x, f₁ x = fderiv ℝ (⇑f) x v) → f₁ ∈ N) →
    (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ N → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ N) →
    ∃ W : Submodule ℂ (SchwartzMap E ℂ), W ≤ N ∧ G ∈ W ∧
      (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ W → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ W) ∧
      (∀ f ∈ W, 𝓕 f ∈ W) := by
  intro E _ _ _ _ _ N G hG hGN hD hL
  let S : Set (Submodule ℂ (SchwartzMap E ℂ)) := {K | G ∈ K ∧
    (∀ (v : E) (f f₁ : SchwartzMap E ℂ), f ∈ K → (∀ x, f₁ x = fderiv ℝ (⇑f) x v) → f₁ ∈ K) ∧
    (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ K → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ K)}
  have hWG : G ∈ sInf S := Submodule.mem_sInf.2 fun K hK => hK.1
  have hWD : ∀ (v : E) (f f₁ : SchwartzMap E ℂ), f ∈ sInf S →
      (∀ x, f₁ x = fderiv ℝ (⇑f) x v) → f₁ ∈ sInf S := fun v f f₁ hf h =>
    Submodule.mem_sInf.2 fun K hK => hK.2.1 v f f₁ (Submodule.mem_sInf.1 hf K hK) h
  have hWL : ∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ sInf S →
      (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ sInf S := fun v f f₁ hf h =>
    Submodule.mem_sInf.2 fun K hK => hK.2.2 v f f₁ (Submodule.mem_sInf.1 hf K hK) h
  have htemp : ∀ m : E, Function.HasTemperateGrowth (fun x : E => inner ℝ x m) := by
    intro m
    have : (fun x : E => inner ℝ x m) = (innerSL ℝ m : E →L[ℝ] ℝ) := by
      funext x; simp [real_inner_comm]
    rw [this]; exact (innerSL ℝ m).hasTemperateGrowth
  have hFG : 𝓕 G = G := by
    ext w
    have h1 : (⇑G) = fun v : E => Complex.exp (-(Real.pi : ℂ) * (‖v‖ : ℂ) ^ 2) := by
      funext v; rw [hG]; congr 1; push_cast; ring
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    rw [SchwartzMap.fourier_coe, h1,
      fourier_gaussian_innerProductSpace (by simpa using Real.pi_pos), div_self hpi,
      Complex.one_cpow, one_mul]
    congr 1
    field_simp
  have hK : (sInf S).comap (SchwartzMap.fourierTransformCLM ℂ (V := E) (E := ℂ)).toLinearMap ∈ S := by
    refine ⟨?_, ?_, ?_⟩
    · show 𝓕 G ∈ sInf S
      rw [hFG]; exact hWG
    · intro v f f₁ hf h
      have hf' : 𝓕 f ∈ sInf S := hf
      show 𝓕 f₁ ∈ sInf S
      have h1 : f₁ = LineDeriv.lineDerivOp v f := by
        ext x; rw [h, SchwartzMap.lineDerivOp_apply_eq_fderiv]
      rw [h1, SchwartzMap.fourier_lineDerivOp_eq]
      refine Submodule.smul_mem _ _ (hWL (innerSL ℝ v) _ _ hf' fun x => ?_)
      rw [SchwartzMap.smulLeftCLM_apply_apply (htemp v)]
      simp [real_inner_comm]
    · intro ℓ f f₁ hf h
      have hf' : 𝓕 f ∈ sInf S := hf
      show 𝓕 f₁ ∈ sInf S
      set u : E := (InnerProductSpace.toDual ℝ E).symm ℓ with hu
      have h1 : f₁ = SchwartzMap.smulLeftCLM ℂ (fun x => inner ℝ x u) f := by
        ext x
        rw [h, SchwartzMap.smulLeftCLM_apply_apply (htemp u), real_inner_comm, hu,
          InnerProductSpace.toDual_symm_apply]
        simp
      have h2 : LineDeriv.lineDerivOp u (𝓕 f) ∈ sInf S :=
        hWD u _ _ hf' fun x => SchwartzMap.lineDerivOp_apply_eq_fderiv _ _ _
      rw [SchwartzMap.lineDerivOp_fourier_eq, ← h1, ← SchwartzMap.fourierTransformCLM_apply ℂ,
        map_smul, SchwartzMap.fourierTransformCLM_apply] at h2
      have hc : (-(2 * (Real.pi : ℂ) * Complex.I)) ≠ 0 := by
        simp [Real.pi_ne_zero]
      exact (Submodule.smul_mem_iff _ hc).1 h2
  exact ⟨sInf S, sInf_le ⟨hGN, hD, hL⟩, hWG, hWL, fun f hf => sInf_le hK hf⟩

end GlobalTheory
end

open FourierTransform MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fourier_stable_submodule_containing_gaussian : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (N : Submodule ℂ (SchwartzMap E ℂ)) (G : SchwartzMap E ℂ),
    (∀ y, G y = Complex.exp (-((Real.pi * ‖y‖ ^ 2 : ℝ) : ℂ))) → G ∈ N →
    (∀ (v : E) (f f₁ : SchwartzMap E ℂ), f ∈ N → (∀ x, f₁ x = fderiv ℝ (⇑f) x v) → f₁ ∈ N) →
    (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ N → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ N) →
    ∃ W : Submodule ℂ (SchwartzMap E ℂ), W ≤ N ∧ G ∈ W ∧
      (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ W → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ W) ∧
      (∀ f ∈ W, 𝓕 f ∈ W) := by
  atlas_forward_decl GlobalTheory.exists_fourier_stable_gaussian_submodule
end

section
section
open FourierTransform MeasureTheory Filter Topology

namespace GlobalTheory

theorem topologicalClosure_stable_of_continuousLinearMap {M : Type} [TopologicalSpace M] [AddCommGroup M]
    [Module ℂ M] [ContinuousSMul ℂ M] [ContinuousAdd M] (W : Submodule ℂ M) (T : M →L[ℂ] M)
    (hT : ∀ f ∈ W, T f ∈ W) : ∀ f ∈ W.topologicalClosure, T f ∈ W.topologicalClosure := by
  intro f hf
  have h1 : Submodule.map (T : M →ₗ[ℂ] M) W ≤ W := by
    rintro _ ⟨g, hg, rfl⟩
    exact hT g hg
  have h2 := Submodule.topologicalClosure_map T W
  exact Submodule.topologicalClosure_mono h1 (h2 ⟨f, hf, rfl⟩)

theorem schwartz_closure_stable_linearForm_fourier :
    ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (W : Submodule ℂ (SchwartzMap E ℂ)),
    (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ W → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ W) →
    (∀ f ∈ W, 𝓕 f ∈ W) →
    (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ W.topologicalClosure → (∀ x, f₁ x = (ℓ x : ℂ) * f x) →
      f₁ ∈ W.topologicalClosure) ∧
    (∀ f ∈ W.topologicalClosure, 𝓕 f ∈ W.topologicalClosure) := by
  intro E _ _ _ _ _ W hmul hF
  constructor
  · intro ℓ f f₁ hf hf₁
    have hg : Function.HasTemperateGrowth (fun x : E => ((ℓ x : ℝ) : ℂ)) :=
      (Complex.ofRealCLM.comp ℓ).hasTemperateGrowth
    set T : SchwartzMap E ℂ →L[ℂ] SchwartzMap E ℂ :=
      SchwartzMap.smulLeftCLM ℂ (fun x : E => ((ℓ x : ℝ) : ℂ)) with hTdef
    have hTapp : ∀ g : SchwartzMap E ℂ, ∀ x, T g x = (ℓ x : ℂ) * g x := by
      intro g x
      rw [hTdef, SchwartzMap.smulLeftCLM_apply hg]
      rfl
    have hTW : ∀ g ∈ W, T g ∈ W := fun g hg' => hmul ℓ g (T g) hg' (hTapp g)
    have hf₁T : f₁ = T f := by
      ext x
      rw [hf₁ x, hTapp f x]
    rw [hf₁T]
    exact topologicalClosure_stable_of_continuousLinearMap W T hTW f hf
  · intro f hf
    have hTW : ∀ g ∈ W, SchwartzMap.fourierTransformCLM ℂ g ∈ W := by
      intro g hg
      rw [SchwartzMap.fourierTransformCLM_apply]
      exact hF g hg
    have := topologicalClosure_stable_of_continuousLinearMap W (SchwartzMap.fourierTransformCLM ℂ) hTW f hf
    rwa [SchwartzMap.fourierTransformCLM_apply] at this

end GlobalTheory
end

open FourierTransform MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topologicalClosure_stable_linearForm_mul_and_fourier : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (W : Submodule ℂ (SchwartzMap E ℂ)),
    (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ W → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ W) →
    (∀ f ∈ W, 𝓕 f ∈ W) →
    (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ W.topologicalClosure → (∀ x, f₁ x = (ℓ x : ℂ) * f x) →
      f₁ ∈ W.topologicalClosure) ∧
    (∀ f ∈ W.topologicalClosure, 𝓕 f ∈ W.topologicalClosure) := by
  atlas_forward_decl GlobalTheory.schwartz_closure_stable_linearForm_fourier
end

section
section
open FourierTransform MeasureTheory Filter Topology

theorem GlobalTheory.GaussWidths.all_widths : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (M : Submodule ℂ (SchwartzMap E ℂ)), IsClosed (M : Set (SchwartzMap E ℂ)) →
    (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ M → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ M) →
    (∀ f ∈ M, 𝓕 f ∈ M) →
    ∀ G : SchwartzMap E ℂ, (∀ y, G y = Complex.exp (-((Real.pi * ‖y‖ ^ 2 : ℝ) : ℂ))) → G ∈ M →
    ∀ (c : ℝ), 0 < c → ∀ g : SchwartzMap E ℂ, (∀ y, g y = Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) → g ∈ M :=
  GlobalTheory.GaussWidths.all_widths_of_conv GlobalTheory.T.mem_of_closedSubmodule_gaussian_convolution
end

open FourierTransform MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_all_gaussianWidths_of_fourierStable_schwartz : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (M : Submodule ℂ (SchwartzMap E ℂ)), IsClosed (M : Set (SchwartzMap E ℂ)) →
    (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ M → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ M) →
    (∀ f ∈ M, 𝓕 f ∈ M) →
    ∀ G : SchwartzMap E ℂ, (∀ y, G y = Complex.exp (-((Real.pi * ‖y‖ ^ 2 : ℝ) : ℂ))) → G ∈ M →
    ∀ (c : ℝ), 0 < c → ∀ g : SchwartzMap E ℂ, (∀ y, g y = Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) → g ∈ M := by
  atlas_forward_decl GlobalTheory.GaussWidths.all_widths
end

section
section
open FourierTransform MeasureTheory Filter Topology
open scoped ContDiff Nat SchwartzMap

noncomputable section

namespace GlobalTheory.GaussCutoff

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def cutErr (c : ℝ) (y : E) : ℂ := GroundTheory.Global.gaussianSchwartz E (c • y) - 1

theorem contDiff_cutErr (c : ℝ) : ContDiff ℝ ∞ (cutErr (E := E) c) :=
  (((GroundTheory.Global.gaussianSchwartz E).smooth ⊤).comp (contDiff_const_smul c)).sub contDiff_const

theorem norm_cutErr_le (c : ℝ) (y : E) : ‖cutErr c y‖ ≤ Real.pi * c ^ 2 * ‖y‖ ^ 2 := by
  unfold cutErr
  rw [GroundTheory.Global.gaussianSchwartz_apply]
  have hx : ‖c • y‖ ^ 2 = c ^ 2 * ‖y‖ ^ 2 := by rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  rw [hx]
  set a := Real.pi * c ^ 2 * ‖y‖ ^ 2 with ha_def
  have ha : 0 ≤ a := by positivity
  have h1 : Real.exp (-Real.pi * (c ^ 2 * ‖y‖ ^ 2)) = Real.exp (-a) := by
    congr 1; rw [ha_def]; ring
  have he : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.2 (neg_nonpos.2 ha)
  rw [h1, show ((Real.exp (-a) : ℝ) : ℂ) - 1 = ((Real.exp (-a) - 1 : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
  linarith [Real.add_one_le_exp (-a)]

theorem norm_iteratedFDeriv_cutErr_le (c : ℝ) {j : ℕ} (hj : j ≠ 0) (y : E) :
    ‖iteratedFDeriv ℝ j (cutErr c) y‖ ≤
      |c| ^ j * SchwartzMap.seminorm ℝ 0 j (GroundTheory.Global.gaussianSchwartz E) := by
  set g := GroundTheory.Global.gaussianSchwartz E with hg
  set L : E →L[ℝ] E := c • ContinuousLinearMap.id ℝ E with hL
  have hgL : ContDiff ℝ ∞ ((g : E → ℂ) ∘ L) := (g.smooth ⊤).comp L.contDiff
  have hfun : cutErr (E := E) c = ((g : E → ℂ) ∘ L) - fun _ => (1 : ℂ) := by
    funext z; simp [cutErr, hL, hg]
  rw [hfun, iteratedFDeriv_sub_apply (hgL.contDiffAt.of_le (by exact_mod_cast le_top)) contDiffAt_const,
    iteratedFDeriv_const_of_ne hj, Pi.zero_apply, sub_zero,
    L.iteratedFDeriv_comp_right (g.smooth ⊤) y (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hLn : ‖L‖ ≤ |c| := by
    rw [hL]; refine (norm_smul_le _ _).trans ?_
    rw [Real.norm_eq_abs]; exact mul_le_of_le_one_right (abs_nonneg c) ContinuousLinearMap.norm_id_le
  have hD : ‖iteratedFDeriv ℝ j g (L y)‖ ≤ SchwartzMap.seminorm ℝ 0 j g := by
    simpa using SchwartzMap.le_seminorm ℝ 0 j g (L y)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_comm]
  exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hLn j) hD (norm_nonneg _)
    (pow_nonneg (abs_nonneg c) j)

theorem norm_iteratedFDeriv_cutErr_le' (c : ℝ) (hc : |c| ≤ 1) (j : ℕ) (y : E) :
    ‖iteratedFDeriv ℝ j (cutErr c) y‖ ≤
      |c| * (Real.pi + SchwartzMap.seminorm ℝ 0 j (GroundTheory.Global.gaussianSchwartz E)) * (1 + ‖y‖) ^ 2 := by
  have hS : 0 ≤ SchwartzMap.seminorm ℝ 0 j (GroundTheory.Global.gaussianSchwartz E) := apply_nonneg _ _
  have hy : 0 ≤ ‖y‖ := norm_nonneg y
  have hc0 : 0 ≤ |c| := abs_nonneg c
  have hpi := Real.pi_pos
  have h1 : 1 ≤ (1 + ‖y‖) ^ 2 := one_le_pow₀ (by linarith)
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [norm_iteratedFDeriv_zero]
    refine (norm_cutErr_le c y).trans ?_
    have hc2 : c ^ 2 ≤ |c| := by rw [← sq_abs]; nlinarith
    have hy2 : ‖y‖ ^ 2 ≤ (1 + ‖y‖) ^ 2 := by nlinarith
    calc Real.pi * c ^ 2 * ‖y‖ ^ 2 ≤ Real.pi * |c| * (1 + ‖y‖) ^ 2 := by gcongr
      _ = |c| * Real.pi * (1 + ‖y‖) ^ 2 := by ring
      _ ≤ _ := by gcongr; linarith
  · refine (norm_iteratedFDeriv_cutErr_le c hj.ne' y).trans ?_
    have hcj : |c| ^ j ≤ |c| := pow_le_of_le_one hc0 hc hj.ne'
    calc |c| ^ j * SchwartzMap.seminorm ℝ 0 j (GroundTheory.Global.gaussianSchwartz E)
        ≤ |c| * SchwartzMap.seminorm ℝ 0 j (GroundTheory.Global.gaussianSchwartz E) := by gcongr
      _ ≤ |c| * (Real.pi + SchwartzMap.seminorm ℝ 0 j (GroundTheory.Global.gaussianSchwartz E)) * 1 := by
          rw [mul_one]; gcongr; linarith
      _ ≤ _ := by gcongr

theorem cut_bound (h : 𝓢(E, ℂ)) (k n : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ c : ℝ, |c| ≤ 1 → ∀ y : E,
    ‖y‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => cutErr c y * h y) y‖ ≤ |c| * K := by
  set S : ℕ → ℝ := fun i => SchwartzMap.seminorm ℝ 0 i (GroundTheory.Global.gaussianSchwartz E) with hS
  set P := (Finset.Iic (k + 2, n)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) h with hP_def
  have hP : 0 ≤ P := apply_nonneg _ _
  have hS0 : ∀ i, 0 ≤ S i := fun i => apply_nonneg _ _
  have hpi := Real.pi_pos
  refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (Real.pi + S i) * (2 ^ (k + 2) * P),
    Finset.sum_nonneg fun i _ => by have := hS0 i; positivity, fun c hc y => ?_⟩
  have hy : 0 ≤ ‖y‖ := norm_nonneg y
  have hL := norm_iteratedFDeriv_mul_le (contDiff_cutErr (E := E) c) (h.smooth ⊤) y (n := n)
    (by exact_mod_cast le_top)
  calc ‖y‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => cutErr c y * h y) y‖
      ≤ ‖y‖ ^ k * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (cutErr c) y‖ *
          ‖iteratedFDeriv ℝ (n - i) h y‖ := by gcongr
    _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (‖iteratedFDeriv ℝ i (cutErr c) y‖ *
          (‖y‖ ^ k * ‖iteratedFDeriv ℝ (n - i) h y‖)) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; ring
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ((|c| * (Real.pi + S i)) *
          ((1 + ‖y‖) ^ 2 * (‖y‖ ^ k * ‖iteratedFDeriv ℝ (n - i) h y‖))) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have := norm_iteratedFDeriv_cutErr_le' c hc i y
        have h0 : 0 ≤ ‖y‖ ^ k * ‖iteratedFDeriv ℝ (n - i) h y‖ := by positivity
        have e : |c| * (Real.pi + S i) * ((1 + ‖y‖) ^ 2 * (‖y‖ ^ k * ‖iteratedFDeriv ℝ (n - i) h y‖)) =
          (|c| * (Real.pi + S i) * (1 + ‖y‖) ^ 2) * (‖y‖ ^ k * ‖iteratedFDeriv ℝ (n - i) h y‖) := by ring
        rw [e]; gcongr
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ((|c| * (Real.pi + S i)) * (2 ^ (k + 2) * P)) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hS0i := hS0 i
        have hX : (1 + ‖y‖) ^ 2 * (‖y‖ ^ k * ‖iteratedFDeriv ℝ (n - i) h y‖) ≤ 2 ^ (k + 2) * P := by
          calc (1 + ‖y‖) ^ 2 * (‖y‖ ^ k * ‖iteratedFDeriv ℝ (n - i) h y‖)
              ≤ (1 + ‖y‖) ^ 2 * ((1 + ‖y‖) ^ k * ‖iteratedFDeriv ℝ (n - i) h y‖) := by
                gcongr; linarith
            _ = (1 + ‖y‖) ^ (k + 2) * ‖iteratedFDeriv ℝ (n - i) h y‖ := by ring
            _ ≤ 2 ^ (k + 2) * P :=
                SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k + 2, n)) le_rfl
                  (Nat.sub_le n i) h y
        gcongr
    _ = |c| * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (Real.pi + S i) * (2 ^ (k + 2) * P) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; ring

def cutMap (h : 𝓢(E, ℂ)) (c : ℝ) (hc : |c| ≤ 1) : 𝓢(E, ℂ) where
  toFun y := cutErr c y * h y
  smooth' := (contDiff_cutErr c).mul (h.smooth ⊤)
  decay' k n := by
    obtain ⟨K, -, hK⟩ := cut_bound h k n
    exact ⟨|c| * K, hK c hc⟩

theorem cutMap_apply (h : 𝓢(E, ℂ)) (c : ℝ) (hc : |c| ≤ 1) (y : E) :
    cutMap h c hc y = cutErr c y * h y := rfl

end GlobalTheory.GaussCutoff

open GlobalTheory.GaussCutoff in

theorem GlobalTheory.GaussCutoff.mem_closure_gauss_mul (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (h : SchwartzMap E ℂ) :
    h ∈ closure {u : SchwartzMap E ℂ | ∃ b : ℝ, 0 < b ∧ ∀ y, u y = Complex.exp (-((b * ‖y‖ ^ 2 : ℝ) : ℂ)) * h y} := by
  rw [mem_closure_iff_nhds]
  intro U hU
  obtain ⟨s, r, hr, hsub⟩ := ((schwartz_withSeminorms ℝ E ℂ).mem_nhds_iff h U).1 hU
  choose K hK0 hK using fun m : ℕ × ℕ => cut_bound h m.1 m.2
  set M := ∑ m ∈ s, K m with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun m _ => hK0 m
  set c := min 1 (r / (2 * (M + 1))) with hc_def
  have hcpos : 0 < c := lt_min one_pos (by positivity)
  have hc1 : |c| ≤ 1 := by rw [abs_of_pos hcpos]; exact min_le_left _ _
  have hcr : c * (M + 1) ≤ r / 2 := by
    have := min_le_right 1 (r / (2 * (M + 1)))
    rw [← hc_def] at this
    calc c * (M + 1) ≤ r / (2 * (M + 1)) * (M + 1) := by gcongr
      _ = r / 2 := by field_simp
  refine ⟨h + cutMap h c hc1, hsub ?_, Real.pi * c ^ 2, by positivity, fun y => ?_⟩
  · rw [Seminorm.mem_ball, add_sub_cancel_left]
    refine Seminorm.finset_sup_apply_lt hr fun m hm => ?_
    have h1 : SchwartzMap.seminorm ℝ m.1 m.2 (cutMap h c hc1) ≤ |c| * K m :=
      SchwartzMap.seminorm_le_bound ℝ m.1 m.2 _ (mul_nonneg (abs_nonneg c) (hK0 m)) (hK m c hc1)
    have h2 : K m ≤ M := Finset.single_le_sum (fun m _ => hK0 m) hm
    show SchwartzMap.seminorm ℝ m.1 m.2 (cutMap h c hc1) < r
    rw [abs_of_pos hcpos] at h1
    nlinarith
  · rw [add_apply, cutMap_apply, cutErr, GroundTheory.Global.gaussianSchwartz_apply, Complex.ofReal_exp]
    have e : -Real.pi * ‖c • y‖ ^ 2 = -(Real.pi * c ^ 2 * ‖y‖ ^ 2) := by
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]; ring
    rw [e]; push_cast; ring
end
end

open FourierTransform MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_closure_wideGaussian_mul_schwartz : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (h : SchwartzMap E ℂ),
    h ∈ closure {u : SchwartzMap E ℂ | ∃ b : ℝ, 0 < b ∧ ∀ y, u y = Complex.exp (-((b * ‖y‖ ^ 2 : ℝ) : ℂ)) * h y} := by
  atlas_forward_decl GlobalTheory.GaussCutoff.mem_closure_gauss_mul
end

section
section
open FourierTransform MeasureTheory Filter Topology

namespace GlobalTheory.NarrowGauss

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

noncomputable def gauss (c : ℝ) (hc : 0 < c) : SchwartzMap E ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    ((LinearEquiv.smulOfNeZero ℝ E (Real.sqrt (c / Real.pi))
      (Real.sqrt_ne_zero'.2 (div_pos hc Real.pi_pos))).toContinuousLinearEquiv)
    (GroundTheory.Global.gaussianSchwartz E)

theorem gauss_apply (c : ℝ) (hc : 0 < c) (x : E) :
    gauss c hc x = Complex.exp (-(c : ℂ) * ‖x‖ ^ 2) := by
  rw [gauss, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    GroundTheory.Global.gaussianSchwartz_apply]
  have h : -Real.pi * ‖(LinearEquiv.smulOfNeZero ℝ E (Real.sqrt (c / Real.pi))
      (Real.sqrt_ne_zero'.2 (div_pos hc Real.pi_pos))).toContinuousLinearEquiv x‖ ^ 2
      = -c * ‖x‖ ^ 2 := by
    simp only [LinearEquiv.coe_toContinuousLinearEquiv', LinearEquiv.smulOfNeZero_apply,
      norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      Real.sq_sqrt (div_pos hc Real.pi_pos).le]
    field_simp
  rw [h, Complex.ofReal_exp]
  push_cast
  ring_nf

theorem fourier_gauss (c : ℝ) (hc : 0 < c) (w : E) :
    (𝓕 (gauss (E := E) c hc) : SchwartzMap E ℂ) w = (Real.pi / (c : ℂ)) ^ (Module.finrank ℝ E / 2 : ℂ) *
      Complex.exp (-Real.pi ^ 2 * ‖w‖ ^ 2 / c) := by
  rw [SchwartzMap.fourier_coe]
  have : (⇑(gauss c hc) : E → ℂ) = fun v ↦ Complex.exp (-(c : ℂ) * ‖v‖ ^ 2) :=
    funext (gauss_apply c hc)
  rw [this, fourier_gaussian_innerProductSpace (by simpa using hc)]

theorem fourierInv_gauss_mul_eq (f u : SchwartzMap E ℂ) (b : ℝ) (hb : 0 < b)
    (hu : ∀ y, u y = Complex.exp (-((b * ‖y‖ ^ 2 : ℝ) : ℂ)) * (𝓕 f : SchwartzMap E ℂ) y) :
    ∃ (c : ℝ) (s : ℂ), 0 < c ∧ ∀ y, (𝓕⁻ u : SchwartzMap E ℂ) y =
      s * ∫ a, f a * Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ)) := by
  set c : ℝ := Real.pi ^ 2 / b with hc_def
  have hc : 0 < c := by positivity
  set K : ℂ := (Real.pi / (c : ℂ)) ^ (Module.finrank ℝ E / 2 : ℂ) with hK
  have hK0 : K ≠ 0 := by
    rw [hK]
    exact Complex.cpow_ne_zero_iff.2 (Or.inl (div_ne_zero (by exact_mod_cast Real.pi_ne_zero)
      (by exact_mod_cast hc.ne')))
  set g : SchwartzMap E ℂ := gauss c hc
  set v : SchwartzMap E ℂ := SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) f g
  have huv : u = K⁻¹ • (𝓕 v : SchwartzMap E ℂ) := by
    ext ξ
    rw [SchwartzMap.smul_apply, SchwartzMap.fourier_convolution, SchwartzMap.pairing_apply_apply,
      ContinuousLinearMap.mul_apply', fourier_gauss, ← hK, hu, smul_eq_mul]
    have e : Complex.exp (-Real.pi ^ 2 * ‖ξ‖ ^ 2 / c) = Complex.exp (-((b * ‖ξ‖ ^ 2 : ℝ) : ℂ)) := by
      congr 1
      rw [hc_def]
      push_cast
      field_simp
    rw [e]
    field_simp
  refine ⟨c, K⁻¹, hc, fun y ↦ ?_⟩
  rw [huv, FourierTransform.fourierInv_smul, FourierTransform.fourierInv_fourier_eq,
    SchwartzMap.smul_apply, smul_eq_mul, SchwartzMap.convolution_apply, convolution_def]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun a ↦ ?_)
  simp only [ContinuousLinearMap.mul_apply', g, gauss_apply]
  push_cast
  ring_nf

end GlobalTheory.NarrowGauss

open GlobalTheory.NarrowGauss in
theorem GlobalTheory.narrowGauss_convolution_dense :
    ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : SchwartzMap E ℂ),
    f ∈ closure {u : SchwartzMap E ℂ | ∃ (c : ℝ) (s : ℂ), 0 < c ∧
      ∀ y, u y = s * ∫ a, f a * Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ))} := by
  intro E _ _ _ _ _ f
  have h1 := GlobalTheory.T.mem_closure_wideGaussian_mul_schwartz E (𝓕 f : SchwartzMap E ℂ)
  have h2 := map_mem_closure (f := fun w : SchwartzMap E ℂ ↦ (𝓕⁻ w : SchwartzMap E ℂ))
    (t := {u : SchwartzMap E ℂ | ∃ (c : ℝ) (s : ℂ), 0 < c ∧
      ∀ y, u y = s * ∫ a, f a * Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ))})
    FourierTransform.continuous_fourierInv h1 (fun u hu ↦ by
      obtain ⟨b, hb, hu⟩ := hu
      exact fourierInv_gauss_mul_eq f u b hb hu)
  simpa [FourierTransform.fourierInv_fourier_eq] using h2
end

open FourierTransform MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_closure_gaussian_convolutions : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : SchwartzMap E ℂ),
    f ∈ closure {u : SchwartzMap E ℂ | ∃ (c : ℝ) (s : ℂ), 0 < c ∧
      ∀ y, u y = s * ∫ a, f a * Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ))} := by
  atlas_forward_decl GlobalTheory.narrowGauss_convolution_dense
end

section
section
open FourierTransform MeasureTheory Filter Topology

namespace GlobalTheory.SchwartzGaussDense

theorem dense_of_stdGaussian_mem : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (N : Submodule ℂ (SchwartzMap E ℂ)) (G : SchwartzMap E ℂ),
    (∀ y, G y = Complex.exp (-((Real.pi * ‖y‖ ^ 2 : ℝ) : ℂ))) → G ∈ N →
    (∀ (v : E) (f f₁ : SchwartzMap E ℂ), f ∈ N → (∀ x, f₁ x = fderiv ℝ (⇑f) x v) → f₁ ∈ N) →
    (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ N → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ N) →
    Dense (N : Set (SchwartzMap E ℂ)) := by
  intro E _ _ _ _ _ N G hG hGN hD hL
  obtain ⟨W, hWN, hGW, hLW, hFW⟩ := GlobalTheory.T.exists_fourier_stable_submodule_containing_gaussian E N G hG hGN hD hL
  obtain ⟨hLM, hFM⟩ := GlobalTheory.T.topologicalClosure_stable_linearForm_mul_and_fourier E W hLW hFW
  set M := W.topologicalClosure with hMdef
  have hcl : IsClosed (M : Set (SchwartzMap E ℂ)) := W.isClosed_topologicalClosure
  have hGM : G ∈ M := W.le_topologicalClosure hGW
  have hgauss := GlobalTheory.T.mem_all_gaussianWidths_of_fourierStable_schwartz E M hcl hLM hFM G hG hGM
  have key : ∀ (h f : SchwartzMap E ℂ), (∃ b : ℝ, 0 < b ∧ ∀ y, f y = Complex.exp (-((b * ‖y‖ ^ 2 : ℝ) : ℂ)) * h y) →
      f ∈ M := by
    rintro h f ⟨b, hb, hf⟩
    have hsub : {u : SchwartzMap E ℂ | ∃ (c : ℝ) (s : ℂ), 0 < c ∧
        ∀ y, u y = s * ∫ a, f a * Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ))} ⊆ (M : Set (SchwartzMap E ℂ)) := by
      rintro u ⟨c, s, hc, hu⟩
      by_cases hs : s = 0
      · have : u = 0 := by ext y; simp [hu y, hs]
        rw [this]; exact M.zero_mem
      · have hu' : ∀ y, (s⁻¹ • u) y = ∫ a, Complex.exp (-((b * ‖a‖ ^ 2 : ℝ) : ℂ)) * h a *
            Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ)) := by
          intro y
          rw [SchwartzMap.smul_apply, hu y, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hs, one_mul]
          congr 1; funext a; rw [hf a]
        have hmem := GlobalTheory.T.mem_of_closedSubmodule_gaussian_convolution E M hcl hLM b c hb hc (hgauss c hc) h (s⁻¹ • u) hu'
        have : u = s • (s⁻¹ • u) := by rw [smul_smul, mul_inv_cancel₀ hs, one_smul]
        rw [this]; exact M.smul_mem s hmem
    exact closure_minimal hsub hcl (GlobalTheory.T.mem_closure_gaussian_convolutions E f)
  have hall : ∀ h : SchwartzMap E ℂ, h ∈ M := by
    intro h
    exact closure_minimal (fun f hf => key h f hf) hcl (GlobalTheory.T.mem_closure_wideGaussian_mul_schwartz E h)
  have htop : N.topologicalClosure = ⊤ := by
    rw [eq_top_iff]
    intro h _
    exact Submodule.topologicalClosure_mono hWN (hall h)
  exact (Submodule.dense_iff_topologicalClosure_eq_top).2 htop

theorem dense_of_gaussian_mem : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (N : Submodule ℂ (SchwartzMap V ℂ))
    (g : SchwartzMap V ℂ) (Q : V →L[ℝ] V →L[ℝ] ℂ) (c : ℝ), 0 < c → (∀ x, c * ‖x‖ ^ 2 ≤ (Q x x).re) →
    (∀ x, g x = Complex.exp (-(Q x x))) → g ∈ N →
    (∀ (v : V) (f f₁ : SchwartzMap V ℂ), f ∈ N → (∀ x, f₁ x = fderiv ℝ (⇑f) x v) → f₁ ∈ N) →
    (∀ (ℓ : V →L[ℝ] ℝ) (f f₁ : SchwartzMap V ℂ), f ∈ N → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ N) →
    Dense (N : Set (SchwartzMap V ℂ)) := by
  intro V _ _ _ N g Q c hc hQ hg hgN hD hL
  obtain ⟨A, hA⟩ := GlobalTheory.T.exists_euclidean_equiv_pi_mul_norm_sq_eq_re V Q c hc hQ
  obtain ⟨N₂, hD₂, hL₂, hG₂, hdense⟩ := GlobalTheory.T.schwartz_density_transport_linearEquiv_chirp V _ A Q N hA hD hL
  apply hdense
  let G := GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ (Fin (Module.finrank ℝ V)))
  have hG : ∀ y, G y = Complex.exp (-((Real.pi * ‖y‖ ^ 2 : ℝ) : ℂ)) := by
    intro y
    simp only [G, GroundTheory.Global.gaussianSchwartz_apply, Complex.ofReal_exp]
    congr 1; push_cast; ring
  exact dense_of_stdGaussian_mem _ N₂ G hG (hG₂ g G hg hgN hG) hD₂ hL₂

end GlobalTheory.SchwartzGaussDense
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzSubmodule_eq_top_of_gaussian_mem_derivStable : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (N : Submodule ℂ (SchwartzMap V ℂ))
    (g : SchwartzMap V ℂ) (Q : V →L[ℝ] V →L[ℝ] ℂ) (c : ℝ), 0 < c → (∀ x, c * ‖x‖ ^ 2 ≤ (Q x x).re) →
    (∀ x, g x = Complex.exp (-(Q x x))) → g ∈ N →
    (∀ (v : V) (f f₁ : SchwartzMap V ℂ), f ∈ N → (∀ x, f₁ x = fderiv ℝ (⇑f) x v) → f₁ ∈ N) →
    (∀ (ℓ : V →L[ℝ] ℝ) (f f₁ : SchwartzMap V ℂ), f ∈ N → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ N) →
    Dense (N : Set (SchwartzMap V ℂ)) := by
  atlas_forward_decl GlobalTheory.SchwartzGaussDense.dense_of_gaussian_mem
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.PolDense

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

theorem mem_pol_of_isGauss (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    {f₀ : SInf F (Fin n × Fin d)} (h : M.IsGauss ψ τ f₀) : f₀ ∈ M.Pol ψ τ :=
  Submodule.mem_sInf.2 fun _ hN => hN.1 f₀ h

theorem mem_pol_of_actsD (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    {u : Matrix (Fin n) (Fin d) (AE F E)} (hu : At (evI F) u) {f f₁ : SInf F (Fin n × Fin d)} (hf : f ∈ M.Pol ψ τ)
    (h : ActsD (evI F) (M.heisLine ψ u) f f₁) : f₁ ∈ M.Pol ψ τ :=
  Submodule.mem_sInf.2 fun N hN => hN.2 u hu f (Submodule.mem_sInf.1 hf N hN) f₁ h

open scoped Classical in

theorem pol_stable (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (v a : Fin n × Fin d → mixedEmbedding.mixedSpace F) {f f₁ : SInf F (Fin n × Fin d)} (hf : f ∈ M.Pol ψ τ)
    (h₁ : ∀ y, f₁ y = fderiv ℝ (⇑f) y v - 2 * Real.pi * Complex.I * (GlobalTheory.ArchUniq.trP F (Fin n × Fin d) y a : ℂ) * f y) :
    f₁ ∈ M.Pol ψ τ := by
  obtain ⟨u, hu, hD⟩ := GlobalTheory.HeisDerivArch.exists_heisLine_actsD_eq M ψ hψ (v, a)
  obtain ⟨D, hDa⟩ := GlobalTheory.HeisDeriv.exists_actsD_heisLine M ψ hψ u hu
  have e : D f = f₁ := by
    refine SchwartzMap.ext fun y => ?_
    rw [hD f (D f) (hDa f) y, h₁ y]
  exact e ▸ mem_pol_of_actsD M ψ τ hu hf (hDa f)

open scoped Classical in

theorem pol_dense : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → Dense (M.Pol B.ψ B.emb : Set (SInf F (Fin n × Fin d))) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP
  have hψ : IsStd B.ψ := hP.base.std
  obtain ⟨g, hg, Q, c, hc, hQ, hgQ⟩ := GlobalTheory.T.exists_gaussVacuum_nondegenerate_gaussian_dualPair F E σ B n d X W M χX χW om r s r' s' hP
  refine GlobalTheory.T.schwartzSubmodule_eq_top_of_gaussian_mem_derivStable _ _ g Q c hc hQ hgQ (mem_pol_of_isGauss M B.ψ B.emb hg) ?_ ?_
  · intro v f f₁ hf h₁
    refine pol_stable M B.ψ hψ B.emb v 0 hf fun y => ?_
    rw [h₁ y]
    simp [GlobalTheory.ArchUniq.trP]
  · intro ℓ f f₁ hf h₁
    have hnd := GlobalTheory.ArchSch.mixedTracePairing_nondegenerate F (Fin n × Fin d)
    obtain ⟨a, ha⟩ : ∃ a, ∀ y, GlobalTheory.ArchUniq.trP F (Fin n × Fin d) y a = ℓ y := by
      let e := (GlobalTheory.ArchSch.trP F (Fin n × Fin d)).flip.toDual hnd.flip
      refine ⟨e.symm ℓ.toLinearMap, fun y => ?_⟩
      calc GlobalTheory.ArchUniq.trP F (Fin n × Fin d) y (e.symm ℓ.toLinearMap) = e (e.symm ℓ.toLinearMap) y := by
            simp only [e, LinearMap.BilinForm.toDual_def]; rfl
        _ = ℓ y := by rw [e.apply_symm_apply]; rfl
    have hmem : (-(2 * Real.pi * Complex.I)) • f₁ ∈ M.Pol B.ψ B.emb := by
      refine pol_stable M B.ψ hψ B.emb 0 a hf fun y => ?_
      simp [h₁ y, ha y]
      ring
    have hne : (-(2 * Real.pi * Complex.I)) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have := (M.Pol B.ψ B.emb).smul_mem (-(2 * Real.pi * Complex.I))⁻¹ hmem
    rwa [inv_smul_smul₀ hne] at this

end GlobalTheory.PolDense
end
