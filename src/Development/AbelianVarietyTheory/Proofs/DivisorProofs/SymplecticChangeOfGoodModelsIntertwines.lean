import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActFromBlocks
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantFinprodSchwartzBruhatFiniteAdel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFinprodSchwartzBruhatFiniteAdel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSchwartzNeZeroAtOrigin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroComplementaryAdelicSchwartzFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergEigenLatticePointAtPlaceLocalIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLocalImageLatticeSupportedAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeLocalDarbouxCoordsBounded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergEigenProportionalLocalField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatFiniteAdelesMemSpanRestrictedProdu
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzDeterminedBySchrodingerThetaValues
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergLatticeSelfDualEveryFinitePlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLatticeInvariantVector
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddCharHalfTraceTensorLatticeHeisenbergCocycle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicAddCharEqArchimedeanMulFinprodLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowerUnipotentRealisedOnAdelicSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerMemSchwartzBruhatFinitePlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylElementHasRationalWeilOperatorAdelicFourier

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhat_finiteAdeles_mem_span_restrictedProducts : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∀ g ∈ SB (κ → Af F),
    g ∈ Submodule.span ℂ {p : (κ → Af F) → ℂ | ∃ φ : ∀ v : Pl F, (κ → Fv F v) → ℂ, (∀ v, φ v ∈ SB (κ → Fv F v)) ∧
      (∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) ∧
      p = fun y => ∏ᶠ v, φ v fun i => evalV F v (y i)} := by
  first | exact @GlobalTheory.SBSpan.mem_span_restrictedProd | exact GlobalTheory.SBSpan.mem_span_restrictedProd | (intros; apply GlobalTheory.SBSpan.mem_span_restrictedProd <;> assumption)
end

section
section
open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

open private exists_symmetric_X_isUnit_det_add_mul_of_symplectic from Mathlib.LinearAlgebra.SymplecticGroup

namespace GlobalTheory.SpGen
open Matrix

theorem upper_unipotent_eq {K : Type} [Field K] {κ : Type} [Fintype κ] [DecidableEq κ]
    (s : Matrix κ κ K) :
    (fromBlocks 1 s 0 1 : Matrix (κ ⊕ κ) (κ ⊕ κ) K) =
      fromBlocks 0 1 (-1) 0 * fromBlocks 1 0 (-s) 1 * fromBlocks 0 1 (-1) 0 *
        fromBlocks (-1) 0 0 (-1) := by
  simp [fromBlocks_multiply]

theorem symplectic_generated_levi_lower_weyl :
    ∀ (K : Type) [Field K] (κ : Type) [Fintype κ] [DecidableEq κ] (P : Matrix (κ ⊕ κ) (κ ⊕ κ) K → Prop),
    (∀ a b, P a → P b → P (a * b)) → (∀ g h : Matrix κ κ K, gᵀ * h = 1 → P (Matrix.fromBlocks g 0 0 h)) →
    (∀ b : Matrix κ κ K, bᵀ = b → P (Matrix.fromBlocks 1 0 b 1)) → P (Matrix.fromBlocks 0 1 (-1) 0) →
    ∀ a : Matrix (κ ⊕ κ) (κ ⊕ κ) K, aᵀ * Matrix.fromBlocks 0 1 (-1) 0 * a = Matrix.fromBlocks 0 1 (-1) 0 → P a := by
  intro K _ κ _ _ P hmul hlevi hlow hJ a ha
  have hup : ∀ s : Matrix κ κ K, sᵀ = s → P (fromBlocks 1 s 0 1) := by
    intro s hs
    rw [upper_unipotent_eq]
    exact hmul _ _ (hmul _ _ (hmul _ _ hJ (hlow _ (by simp [hs]))) hJ) (hlevi _ _ (by simp))
  have hJ0 : (fromBlocks 0 1 (-1) 0 : Matrix (κ ⊕ κ) (κ ⊕ κ) K) = -J κ K := by
    simp [J, fromBlocks_neg]
  have hsp : a ∈ symplecticGroup κ K := by
    rw [SymplecticGroup.mem_iff']
    rw [hJ0] at ha
    simpa [Matrix.mul_neg, Matrix.neg_mul] using ha
  obtain ⟨A, B, C, D, rfl⟩ : ∃ A B C D, a = fromBlocks A B C D :=
    ⟨_, _, _, _, a.fromBlocks_toBlocks.symm⟩
  obtain ⟨X, hX, hu⟩ := exists_symmetric_X_isUnit_det_add_mul_of_symplectic hsp
  have hUX : (fromBlocks 1 X 0 1 : Matrix (κ ⊕ κ) (κ ⊕ κ) K) ∈ symplecticGroup κ K := by
    simp [SymplecticGroup.fromBlocks_mem_iff, hX.eq]
  have hprod : (fromBlocks 1 X 0 1 : Matrix (κ ⊕ κ) (κ ⊕ κ) K) * fromBlocks A B C D =
      fromBlocks (A + X * C) (B + X * D) C D := by
    simp [fromBlocks_multiply]
  generalize hc : A + X * C = c at hu hprod
  have hcT : IsUnit cᵀ.det := by rwa [det_transpose]
  have hLev : (fromBlocks c⁻¹ 0 0 cᵀ : Matrix (κ ⊕ κ) (κ ⊕ κ) K) ∈ symplecticGroup κ K := by
    rw [SymplecticGroup.fromBlocks_mem_iff]
    refine ⟨by simp, by simp, ?_⟩
    rw [transpose_nonsing_inv]
    simp [nonsing_inv_mul _ hcT]
  have hnsp := mul_mem (mul_mem hLev hUX) hsp
  have hn : (fromBlocks c⁻¹ 0 0 cᵀ : Matrix (κ ⊕ κ) (κ ⊕ κ) K) * fromBlocks 1 X 0 1 *
      fromBlocks A B C D = fromBlocks 1 (c⁻¹ * (B + X * D)) (cᵀ * C) (cᵀ * D) := by
    rw [Matrix.mul_assoc, hprod, fromBlocks_multiply]
    simp [nonsing_inv_mul _ hu]
  rw [hn] at hnsp
  generalize c⁻¹ * (B + X * D) = Z at hn hnsp
  generalize cᵀ * C = Wm at hn hnsp
  generalize cᵀ * D = V at hn hnsp
  obtain ⟨h1, h2, h3⟩ := SymplecticGroup.fromBlocks_mem_iff.1 hnsp
  simp only [transpose_one, Matrix.one_mul, Matrix.mul_one] at h1 h3
  have hW : Wmᵀ = Wm := h1.symm
  rw [hW] at h3
  have hV : V = Wm * Z + 1 := by rw [← h3]; abel
  have hZ : Zᵀ = Z := by
    rw [hV, transpose_add, transpose_mul, hW, transpose_one, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_one, Matrix.one_mul, ← Matrix.mul_assoc] at h2
    simpa using h2
  have hfac : (fromBlocks 1 Z Wm V : Matrix (κ ⊕ κ) (κ ⊕ κ) K) =
      fromBlocks 1 0 Wm 1 * fromBlocks 1 Z 0 1 := by
    rw [fromBlocks_multiply, hV]; simp
  have e2 : (fromBlocks c 0 0 cᵀ⁻¹ : Matrix (κ ⊕ κ) (κ ⊕ κ) K) * fromBlocks c⁻¹ 0 0 cᵀ = 1 := by
    rw [fromBlocks_multiply]
    simp [mul_nonsing_inv _ hu, nonsing_inv_mul _ hcT]
  have e3 : (fromBlocks 1 (-X) 0 1 : Matrix (κ ⊕ κ) (κ ⊕ κ) K) * fromBlocks 1 X 0 1 = 1 := by
    simp [fromBlocks_multiply]
  have hdec : fromBlocks A B C D = (fromBlocks 1 (-X) 0 1 : Matrix (κ ⊕ κ) (κ ⊕ κ) K) *
      fromBlocks c 0 0 cᵀ⁻¹ * (fromBlocks c⁻¹ 0 0 cᵀ * fromBlocks 1 X 0 1 * fromBlocks A B C D) := by
    rw [Matrix.mul_assoc (fromBlocks 1 (-X) 0 1), ← Matrix.mul_assoc (fromBlocks c 0 0 cᵀ⁻¹),
      ← Matrix.mul_assoc (fromBlocks c 0 0 cᵀ⁻¹), e2, Matrix.one_mul, ← Matrix.mul_assoc, e3,
      Matrix.one_mul]
  rw [hdec, hn, hfac]
  refine hmul _ _ (hmul _ _ (hup _ (by simp [hX.eq])) (hlevi _ _ ?_)) (hmul _ _ (hlow _ hW) (hup _ hZ))
  exact mul_nonsing_inv _ hcT

end GlobalTheory.SpGen
end

open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplecticGroup_generated_levi_lowerUnipotent_weyl : ∀ (K : Type) [Field K] (κ : Type) [Fintype κ] [DecidableEq κ] (P : Matrix (κ ⊕ κ) (κ ⊕ κ) K → Prop),
    (∀ a b, P a → P b → P (a * b)) → (∀ g h : Matrix κ κ K, gᵀ * h = 1 → P (Matrix.fromBlocks g 0 0 h)) →
    (∀ b : Matrix κ κ K, bᵀ = b → P (Matrix.fromBlocks 1 0 b 1)) → P (Matrix.fromBlocks 0 1 (-1) 0) →
    ∀ a : Matrix (κ ⊕ κ) (κ ⊕ κ) K, aᵀ * Matrix.fromBlocks 0 1 (-1) 0 * a = Matrix.fromBlocks 0 1 (-1) 0 → P a := by
  atlas_forward_decl GlobalTheory.SpGen.symplectic_generated_levi_lower_weyl
end

section
section
open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

noncomputable section

namespace GlobalTheory.RatWeilOp

variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem levi_transpose_mul {R : Type} [CommRing R] {g h : Matrix κ κ R} (hg : gᵀ * h = 1) : hᵀ * g = 1 := by
  rw [← Matrix.transpose_transpose (hᵀ * g), Matrix.transpose_mul, Matrix.transpose_transpose, hg, Matrix.transpose_one]

theorem levi_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {g h : Matrix κ κ R} (hg : gᵀ * h = 1) :
    (g.map f)ᵀ * h.map f = 1 := by
  rw [← Matrix.transpose_map, ← Matrix.map_mul, hg, Matrix.map_one _ (map_zero f) (map_one f)]

theorem schr_mulVec_transpose {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {g h : Matrix κ κ R}
    (hg : gᵀ * h = 1) (w : (κ → R) × (κ → R)) (Φ : (κ → R) → ℂ) (x : κ → R) :
    schr ψ w Φ (hᵀ *ᵥ x) = schr ψ (g *ᵥ w.1, h *ᵥ w.2) (fun y => Φ (hᵀ *ᵥ y)) x := by
  have h1 := levi_transpose_mul hg
  have e1 : x ⬝ᵥ h *ᵥ w.2 = (hᵀ *ᵥ x) ⬝ᵥ w.2 := by rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
  have e2 : (g *ᵥ w.1) ⬝ᵥ h *ᵥ w.2 = w.1 ⬝ᵥ w.2 := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  have e3 : hᵀ *ᵥ (x + g *ᵥ w.1) = hᵀ *ᵥ x + w.1 := by
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  simp only [schr]
  rw [e1, e2, e3]

theorem funLeft_schr_levi {F R : Type} [Field F] [CommRing R] [Algebra F R] [Invertible (2 : R)] (ψ : AddChar R ℂ)
    {g h : Matrix κ κ F} (hg : gᵀ * h = 1) (w : (κ → R) × (κ → R)) (Φ : (κ → R) → ℂ) :
    LinearMap.funLeft ℂ ℂ (fun x : κ → R => hᵀ.map (algebraMap F R) *ᵥ x) (schr ψ w Φ) =
      schr ψ (act ((Matrix.fromBlocks g 0 0 h).map (algebraMap F R)) w)
        (LinearMap.funLeft ℂ ℂ (fun x : κ → R => hᵀ.map (algebraMap F R) *ᵥ x) Φ) := by
  funext x
  rw [Matrix.fromBlocks_map, act_fromBlocks, Matrix.map_zero _ (map_zero _), Matrix.zero_mulVec, Matrix.zero_mulVec,
    add_zero, zero_add, LinearMap.funLeft_apply, Matrix.transpose_map]
  exact schr_mulVec_transpose ψ (levi_map (algebraMap F R) hg) w Φ x

theorem bijOn_funLeft_homeomorph {X : Type} [TopologicalSpace X] (T : X ≃ₜ X) :
    Set.BijOn (LinearMap.funLeft ℂ ℂ T) (SB X : Set (X → ℂ)) (SB X : Set (X → ℂ)) := by
  have mem : ∀ (S : X ≃ₜ X), ∀ φ ∈ (SB X : Set (X → ℂ)), φ ∘ S ∈ (SB X : Set (X → ℂ)) :=
    fun S φ hφ => ⟨hφ.1.comp_continuous S.continuous, hφ.2.comp_homeomorph S⟩
  refine ⟨fun φ hφ => mem T φ hφ, fun φ _ ψ _ e => LinearMap.funLeft_injective_of_surjective _ _ _ T.surjective e,
    fun φ hφ => ⟨φ ∘ T.symm, mem T.symm φ hφ, ?_⟩⟩
  funext x
  simp [LinearMap.funLeft_apply]

end GlobalTheory.RatWeilOp

noncomputable section

namespace GlobalTheory.RatWeilOp

variable {κ : Type} [Fintype κ] [DecidableEq κ]

def mulVecHomeo {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (M N : Matrix κ κ R)
    (h1 : M * N = 1) (h2 : N * M = 1) : (κ → R) ≃ₜ (κ → R) where
  toFun x := M *ᵥ x
  invFun x := N *ᵥ x
  left_inv x := by simp only [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
  right_inv x := by simp only [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  continuous_toFun := continuous_const.matrix_mulVec continuous_id
  continuous_invFun := continuous_const.matrix_mulVec continuous_id

variable {F : Type} [Field F] [NumberField F]

theorem evI_algebraMap (c : F) : evI F (algebraMap F (AF F) c) = mixedEmbedding F c := by
  rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]; rfl

def evIHom : AF F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (RingHom.fst _ _)

theorem evIHom_apply (a : AF F) : evIHom a = evI F a := rfl

def mulVecR (M : Matrix κ κ (mixedEmbedding.mixedSpace F)) :
    (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F) :=
  (Matrix.mulVecLin M).restrictScalars ℝ

end GlobalTheory.RatWeilOp

noncomputable section

namespace GlobalTheory.RatWeilOp

variable {κ : Type} [Fintype κ] [DecidableEq κ] {F : Type} [Field F] [NumberField F]

def mulVecCLE (M N : Matrix κ κ (mixedEmbedding.mixedSpace F)) (h1 : M * N = 1) (h2 : N * M = 1) :
    (κ → mixedEmbedding.mixedSpace F) ≃L[ℝ] (κ → mixedEmbedding.mixedSpace F) :=
  (LinearEquiv.ofLinear (mulVecR M) (mulVecR N)
    (LinearMap.ext fun x => by
      simp only [mulVecR, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply,
        Matrix.mulVec_mulVec, h1, Matrix.one_mulVec, LinearMap.id_coe, id_eq])
    (LinearMap.ext fun x => by
      simp only [mulVecR, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply,
        Matrix.mulVec_mulVec, h2, Matrix.one_mulVec, LinearMap.id_coe, id_eq])).toContinuousLinearEquiv

theorem mulVecCLE_apply (M N : Matrix κ κ (mixedEmbedding.mixedSpace F)) (h1 : M * N = 1) (h2 : N * M = 1) (x) :
    mulVecCLE M N h1 h2 x = M *ᵥ x := rfl

theorem levi_map_mul {R : Type} [CommRing R] (f : F →+* R) {g h : Matrix κ κ F} (hg : gᵀ * h = 1) :
    hᵀ.map f * g.map f = 1 ∧ g.map f * hᵀ.map f = 1 := by
  have h1 := levi_transpose_mul hg
  have h2 : g * hᵀ = 1 := (Matrix.mul_eq_one_comm_of_card_eq κ κ F rfl).mp h1
  exact ⟨by rw [← Matrix.map_mul, h1, Matrix.map_one _ (map_zero f) (map_one f)],
    by rw [← Matrix.map_mul, h2, Matrix.map_one _ (map_zero f) (map_one f)]⟩

theorem mulVec_mem_integers (v : Pl F) (M : Matrix κ κ (Fv F v))
    (hM : ∀ i j, M i j ∈ v.adicCompletionIntegers F) (x : κ → Fv F v) (hx : ∀ i, x i ∈ v.adicCompletionIntegers F) :
    ∀ i, (M *ᵥ x) i ∈ v.adicCompletionIntegers F :=
  fun i => sum_mem fun j _ => mul_mem (hM i j) (hx j)

end GlobalTheory.RatWeilOp

noncomputable section
namespace GlobalTheory.RatWeilOp
variable {κ : Type} [Fintype κ] [DecidableEq κ] {F : Type} [Field F] [NumberField F]

theorem ind_mulVec (v : Pl F) (M N : Matrix κ κ (Fv F v)) (hNM : N * M = 1)
    (hM : ∀ i j, M i j ∈ v.adicCompletionIntegers F) (hN : ∀ i j, N i j ∈ v.adicCompletionIntegers F) (x : κ → Fv F v) :
    ind κ v (M *ᵥ x) = ind κ v x := by
  have key : (∀ i, (M *ᵥ x) i ∈ v.adicCompletionIntegers F) ↔ ∀ i, x i ∈ v.adicCompletionIntegers F := by
    refine ⟨fun hx => ?_, mulVec_mem_integers v M hM x⟩
    have e : x = N *ᵥ (M *ᵥ x) := by rw [Matrix.mulVec_mulVec, hNM, Matrix.one_mulVec]
    rw [e]
    exact mulVec_mem_integers v N hN _ hx
  unfold ind
  by_cases hx : ∀ i, x i ∈ v.adicCompletionIntegers F
  · have hx' := (key.2 hx)
    rw [Set.indicator_of_mem (show M *ᵥ x ∈ {y : κ → Fv F v | ∀ i, y i ∈ v.adicCompletionIntegers F} from hx'),
      Set.indicator_of_mem (show x ∈ {y : κ → Fv F v | ∀ i, y i ∈ v.adicCompletionIntegers F} from hx)]
    rfl
  · have hx' : ¬ ∀ i, (M *ᵥ x) i ∈ v.adicCompletionIntegers F := fun h' => hx (key.1 h')
    rw [Set.indicator_of_notMem (show M *ᵥ x ∉ {y : κ → Fv F v | ∀ i, y i ∈ v.adicCompletionIntegers F} from hx'),
      Set.indicator_of_notMem (show x ∉ {y : κ → Fv F v | ∀ i, y i ∈ v.adicCompletionIntegers F} from hx)]
end GlobalTheory.RatWeilOp

noncomputable section
namespace GlobalTheory.RatWeilOp
variable {κ : Type} [Fintype κ] [DecidableEq κ] {F : Type} [Field F] [NumberField F]

open scoped Classical in

theorem funLeft_pure_levi {g h : Matrix κ κ F} (hI1 : hᵀ.map (mixedEmbedding F) * g.map (mixedEmbedding F) = 1)
    (hI2 : g.map (mixedEmbedding F) * hᵀ.map (mixedEmbedding F) = 1) (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) :
    LinearMap.funLeft ℂ ℂ (fun x : κ → AF F => hᵀ.map (algebraMap F (AF F)) *ᵥ x) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (mulVecCLE _ _ hI1 hI2) f)
        (fun v => LinearMap.funLeft ℂ ℂ (fun x : κ → Fv F v => hᵀ.map (algebraMap F (Fv F v)) *ᵥ x) (φ v)) := by
  funext x
  simp only [LinearMap.funLeft_apply, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Function.comp_apply,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, mulVecCLE_apply]
  congr 1
  · congr 1
    funext i
    rw [← evIHom_apply, RingHom.map_mulVec, Matrix.map_map]
    have e : (evIHom ∘ algebraMap F (AF F)) = mixedEmbedding F := funext fun c => evI_algebraMap c
    rw [e]
    rfl
  · refine finprod_congr fun v => congrArg (φ v) (funext fun i => ?_)
    rw [← AlgHom.coe_toRingHom, RingHom.map_mulVec, Matrix.map_map]
    have e : ((evFin F v : AF F →+* Fv F v) ∘ algebraMap F (AF F)) = algebraMap F (Fv F v) :=
      funext fun c => (evFin F v).commutes c
    rw [e]
    rfl

theorem thetaSum_funLeft_levi {g h : Matrix κ κ F} (hg : gᵀ * h = 1) (Φ : (κ → AF F) → ℂ) :
    thetaSum F (LinearMap.funLeft ℂ ℂ (fun x : κ → AF F => hᵀ.map (algebraMap F (AF F)) *ᵥ x) Φ) = thetaSum F Φ := by
  simp only [thetaSum, LinearMap.funLeft_apply]
  have e : ∀ ξ : κ → F, (hᵀ.map (algebraMap F (AF F)) *ᵥ fun i => algebraMap F (AF F) (ξ i)) =
      fun i => algebraMap F (AF F) ((hᵀ *ᵥ ξ) i) := fun ξ => funext fun i => (RingHom.map_mulVec _ _ _ _).symm
  simp only [e]
  have h1 := levi_transpose_mul hg
  have h2 : g * hᵀ = 1 := (Matrix.mul_eq_one_comm_of_card_eq κ κ F rfl).mp h1
  let eq : (κ → F) ≃ (κ → F) :=
    { toFun := fun ξ => hᵀ *ᵥ ξ, invFun := fun ξ => g *ᵥ ξ,
      left_inv := fun ξ => by
        simp only [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
      right_inv := fun ξ => by
        simp only [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec] }
  exact Equiv.tsum_eq eq (fun ξ : κ → F => Φ fun i => algebraMap F (AF F) (ξ i))

end GlobalTheory.RatWeilOp

noncomputable section
namespace GlobalTheory.RatWeilOp

open scoped Classical in

theorem hasOp_levi (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (κ : Type) [Fintype κ] [DecidableEq κ]
    (g h : Matrix κ κ F) (hg : gᵀ * h = 1) : HasOp ψ (Matrix.fromBlocks g 0 0 h) := by
  obtain ⟨hI1, hI2⟩ := levi_map_mul (mixedEmbedding F) hg
  have hv : ∀ v : Pl F, (hᵀ.map (algebraMap F (Fv F v))) * g.map (algebraMap F (Fv F v)) = 1 ∧
      g.map (algebraMap F (Fv F v)) * hᵀ.map (algebraMap F (Fv F v)) = 1 := fun v => levi_map_mul _ hg
  refine ⟨LinearMap.funLeft ℂ ℂ (fun x : κ → AF F => hᵀ.map (algebraMap F (AF F)) *ᵥ x), 1,
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (mulVecCLE _ _ hI1 hI2),
    fun v => LinearMap.funLeft ℂ ℂ (fun x : κ → Fv F v => hᵀ.map (algebraMap F (Fv F v)) *ᵥ x),
    one_ne_zero, ?_, fun v => bijOn_funLeft_homeomorph (mulVecHomeo _ _ (hv v).1 (hv v).2),
    fun v w φ _ => funLeft_schr_levi _ hg w φ, ?_, fun f φ _ =>
      ⟨funLeft_pure_levi hI1 hI2 f φ, fun w => funLeft_schr_levi ψ hg w _, by rw [thetaSum_funLeft_levi hg, one_mul]⟩⟩
  · intro f
    refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (mulVecCLE _ _ hI1 hI2).symm f, ?_⟩
    refine DFunLike.ext _ _ fun x => ?_
    simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
      ContinuousLinearEquiv.symm_apply_apply]
  · have hint : ∀ᶠ v : Pl F in cofinite, ∀ i j, algebraMap F (Fv F v) (h i j) ∈ v.adicCompletionIntegers F ∧
        algebraMap F (Fv F v) (g i j) ∈ v.adicCompletionIntegers F :=
      eventually_all.2 fun i => eventually_all.2 fun j =>
        (eventually_algebraMap_mem_integers _).and (eventually_algebraMap_mem_integers _)
    filter_upwards [hint] with v hv'
    funext x
    exact ind_mulVec v _ _ (hv v).2 (fun i j => (hv' j i).1) (fun i j => (hv' i j).2) x

end GlobalTheory.RatWeilOp
end
end
end
end
end
end
end

open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasRationalWeilOperator_leviBlock : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (κ : Type) [Fintype κ] [DecidableEq κ] (g h : Matrix κ κ F), gᵀ * h = 1 →
    HasOp ψ (Matrix.fromBlocks g 0 0 h) := by
  atlas_forward_decl GlobalTheory.RatWeilOp.hasOp_levi
end

section
section
open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

noncomputable section

open scoped Classical

namespace GlobalTheory.ThetaInj

theorem main : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ], ∀ Φ ∈ schA F κ,
    (∀ w : (κ → AF F) × (κ → AF F), thetaSum F (schr ψ w Φ) = 0) → Φ = 0 := by
  intro F _ _ ψ hψ κ _ Φ hΦ h
  have hn : ∀ a, ‖ψ a‖ = 1 := GlobalTheory.StdCharFromIsStd.norm_psi hψ
  obtain ⟨a₀, ha₀⟩ := GlobalTheory.StdCharFromIsStd.exists_ne_one hψ
  let ι : (κ → F) → (κ → AF F) := fun ξ i => algebraMap F (AF F) (ξ i)
  have hι0 : ι 0 = 0 := by funext i; simp [ι]
  funext x
  have hΦx : (fun z => Φ (z + x)) ∈ schA F κ := GlobalTheory.SchwartzTranslate.schA_translate F x hΦ
  have hc : Summable fun ξ => ‖Φ (ι ξ + x)‖ := by
    convert GlobalTheory.WeilM.summable_norm_of_mem_schA F hΦx using 1
  have key := GlobalTheory.SchrodingerUniq.coeff_zero_eq_zero
    (χ := fun (y : κ → AF F) (ξ : κ → F) => ψ (ι ξ ⬝ᵥ y))
    (c := fun ξ => Φ (ι ξ + x)) (fun y ξ => hn _)
    (fun y y' ξ => by simp only [dotProduct_add, AddChar.map_add_eq_mul])
    (fun ξ => by simp only [dotProduct_zero, AddChar.map_zero_eq_one])
    (fun y => by simp only [hι0, zero_dotProduct, AddChar.map_zero_eq_one])
    (fun ξ hξ => by
      obtain ⟨i, hi⟩ := Function.ne_iff.1 hξ
      have hi' : ξ i ≠ 0 := hi
      refine ⟨Pi.single i (algebraMap F (AF F) (ξ i)⁻¹ * a₀), ?_⟩
      show ψ (ι ξ ⬝ᵥ Pi.single i (algebraMap F (AF F) (ξ i)⁻¹ * a₀)) ≠ 1
      rw [dotProduct_single]
      show ψ (algebraMap F (AF F) (ξ i) * (algebraMap F (AF F) (ξ i)⁻¹ * a₀)) ≠ 1
      rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hi', map_one, one_mul]
      exact ha₀)
    hc (fun y => ?_)
  · simpa [hι0] using key
  · have h' := h (x, y)
    simp only [GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.schr, AddChar.map_add_eq_mul] at h'
    set b := ψ (⅟(2 : AF F) * (x ⬝ᵥ y))
    have hb : b ≠ 0 := by
      intro e
      have h1 : ‖b‖ = 1 := hn _
      rw [e, norm_zero] at h1
      exact zero_ne_one h1
    have e2 : ∑' ξ : κ → F, Φ (ι ξ + x) * ψ (ι ξ ⬝ᵥ y) =
        b⁻¹ * ∑' ξ : κ → F, ψ (ι ξ ⬝ᵥ y) * b * Φ (ι ξ + x) := by
      rw [← tsum_mul_left]; congr 1; funext ξ; field_simp
    rw [e2, h', mul_zero]

end GlobalTheory.ThetaInj
end
end

open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_schroedingerTranslates_thetaSum_zero : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ], ∀ Φ ∈ schA F κ,
    (∀ w : (κ → AF F) × (κ → AF F), thetaSum F (schr ψ w Φ) = 0) → Φ = 0 := by
  atlas_forward_decl GlobalTheory.ThetaInj.main
end

section
open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.self_dual_lattice_invariant_vector : ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) (κ : Type) [Fintype κ] (ψ : AddChar (Fv F v) ℂ), Continuous ψ → (∀ t, ‖ψ t‖ = 1) → ψ ≠ 1 →
    ∀ (Λ : AddSubgroup ((κ → Fv F v) × (κ → Fv F v))) (c : Fv F v), c ≠ 0 →
    (∀ w, w ∈ Λ ↔ ∀ l ∈ Λ, ψ (w.1 ⬝ᵥ l.2 - l.1 ⬝ᵥ w.2) = 1) →
    (∀ l ∈ Λ, ∀ i, c * l.1 i ∈ v.adicCompletionIntegers F ∧ c * l.2 i ∈ v.adicCompletionIntegers F) →
    ∀ η : κ → Fv F v, (∀ b : κ → Fv F v, ((0 : κ → Fv F v), b) ∈ Λ → ψ (η ⬝ᵥ b) = 1) → ∃ y, (η, y) ∈ Λ := by
  first | exact @GlobalTheory.SelfDualFirstProjAny.exists_pair_of_annihilator_any | exact GlobalTheory.SelfDualFirstProjAny.exists_pair_of_annihilator_any | (intros; apply GlobalTheory.SelfDualFirstProjAny.exists_pair_of_annihilator_any <;> assumption)
end

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.VacThetaInd

theorem psi_half_symp_theta_indep : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    ∀ (v : Pl F) (θ θ' : 𝓞 E), (θ : E) + σ θ = 1 → (θ' : E) + σ θ' = 1 → ∀ γ ∈ latAtV X W v,
      B.ψ (⅟(2 : AF F) * symp (R := AF F) (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F W.J) γ γ) =
        B.ψ (⅟(2 : AF F) * symp (R := AF F) (cA σ) (inclR (F := F) (AF F) (θ' : E)) (incM F X.J) (incM F W.J) γ γ) := by
  intro F E _ _ _ _ _ σ B n d X W r s r' s' hB hX hW v θ θ' hθ hθ' γ hγ
  have hσ : ∀ x : E, σ (σ x) = x := fun x => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star]
  have hc : ∀ z, cA σ (cA σ z) = z := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [cA, hσ]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hi : ∀ e : E, cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := fun e => rfl
  have ht : cA σ (hTens (cA σ) (incM F X.J) (incM F W.J) γ γ) = -hTens (cA σ) (incM F X.J) (incM F W.J) γ γ :=
    GlobalTheory.VacCocycle.conj_hTens (cA σ) hc (fun i j => by simp only [incM, Matrix.map_apply, hi, hX.herm])
      (fun i j => by simp only [incM, Matrix.map_apply, hi, hW.skew, map_neg]) γ γ
  set t := hTens (cA σ) (incM F X.J) (incM F W.J) γ γ with htdef
  have htr : ∀ z, Algebra.trace (AF F) (AE F E) (cA σ z) = Algebra.trace (AF F) (AE F E) z :=
    GlobalTheory.VacCocycle.trace_conj (cA σ) hc
  set a := inclR (F := F) (AF F) (θ : E) with ha
  set a' := inclR (F := F) (AF F) (θ' : E) with ha'
  have hca : cA σ a = 1 - a := by
    rw [ha, hi, eq_sub_of_add_eq' hθ, map_sub, map_one]
  have hca' : cA σ a' = 1 - a' := by
    rw [ha', hi, eq_sub_of_add_eq' hθ', map_sub, map_one]
  set z := (a - a') * t with hz
  have hcz : cA σ z = z := by
    rw [hz, map_mul, map_sub, hca, hca', ht]; ring
  have h2 : Algebra.trace (AF F) (AE F E) z = 2 * Algebra.trace (AF F) (AE F E) (a * z) := by
    have e1 : Algebra.trace (AF F) (AE F E) (cA σ (a * z)) = Algebra.trace (AF F) (AE F E) (a * z) := htr _
    rw [map_mul, hca, hcz, sub_mul, one_mul, map_sub] at e1
    linear_combination e1
  have hmul : inclR (F := F) (AF F) (((θ * (θ - θ') : 𝓞 E)) : E) = a * (a - a') := by
    rw [ha, ha', ← map_sub, ← map_mul]; push_cast; rfl
  have key : symp (R := AF F) (cA σ) a (incM F X.J) (incM F W.J) γ γ =
      symp (R := AF F) (cA σ) a' (incM F X.J) (incM F W.J) γ γ +
        2 * symp (R := AF F) (cA σ) (inclR (F := F) (AF F) (((θ * (θ - θ') : 𝓞 E)) : E)) (incM F X.J) (incM F W.J) γ γ := by
    simp only [symp, hmul]
    rw [← htdef, mul_assoc, ← hz, ← h2, hz, sub_mul, map_sub]; ring
  have h1 := GlobalTheory.LatVacArith.psi_symp_latAtV σ B X W r s r' s' hB hX hW v (θ * (θ - θ')) 1
    (by rw [map_one]; exact one_mem _) γ hγ γ hγ
  rw [key, mul_add, ← mul_assoc, invOf_mul_self, one_mul, AddChar.map_add_eq_mul, ← one_mul (symp (R := AF F) (cA σ) (inclR (F := F) (AF F) (((θ * (θ - θ') : 𝓞 E)) : E)) (incM F X.J) (incM F W.J) γ γ), h1, mul_one]

end GlobalTheory.VacThetaInd
end
end

section
section
open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

noncomputable section

namespace GlobalTheory.VacThetaIndep

theorem vacuum_character_theta_indep : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    ∀ (v : Pl F) (θ θ' : 𝓞 E), (θ : E) + σ θ = 1 → (θ' : E) + σ θ' = 1 → ∀ γ ∈ latAtV X W v,
      B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F W.J) γ γ) =
        B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ' : E)) (incM F X.J) (incM F W.J) γ γ) :=
  GlobalTheory.VacThetaInd.psi_half_symp_theta_indep

end GlobalTheory.VacThetaIndep

end
end

open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuum_eigenvalue_theta_independent : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    ∀ (v : Pl F) (θ θ' : 𝓞 E), (θ : E) + σ θ = 1 → (θ' : E) + σ θ' = 1 → ∀ γ ∈ latAtV X W v,
      B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F W.J) γ γ) =
        B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ' : E)) (incM F X.J) (incM F W.J) γ γ) := by
  atlas_forward_decl GlobalTheory.VacThetaIndep.vacuum_character_theta_indep
end

section
section
noncomputable section

open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

namespace GlobalTheory.RatWeilUnip

open GlobalTheory.AdelicSvNQuad (quad map_quad quad_neg quad_add continuous_quad archMul archMul_temperate)

def mulQ {R κ : Type} [CommRing R] [Fintype κ] (χ : AddChar R ℂ) (h : R) (A : Matrix κ κ R) :
    ((κ → R) → ℂ) →ₗ[ℂ] ((κ → R) → ℂ) where
  toFun φ x := χ (quad h A x) * φ x
  map_add' φ φ' := funext fun x => mul_add _ _ _
  map_smul' a φ := funext fun x => by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem mulQ_apply {R κ : Type} [CommRing R] [Fintype κ] (χ : AddChar R ℂ) (h : R) (A : Matrix κ κ R)
    (φ : (κ → R) → ℂ) (x : κ → R) : mulQ χ h A φ x = χ (quad h A x) * φ x := rfl

theorem mulQ_neg_mulQ {R κ : Type} [CommRing R] [Fintype κ] (χ : AddChar R ℂ) (h : R) (A : Matrix κ κ R)
    (φ : (κ → R) → ℂ) : mulQ χ h (-A) (mulQ χ h A φ) = φ := by
  funext x
  rw [mulQ_apply, mulQ_apply, ← mul_assoc, ← AddChar.map_add_eq_mul, quad_neg, neg_add_cancel,
    AddChar.map_zero_eq_one, one_mul]

theorem mulQ_schr {R κ : Type} [CommRing R] [Invertible (2 : R)] [Fintype κ] (χ : AddChar R ℂ) (B : Matrix κ κ R)
    (hB : Bᵀ = B) (w : (κ → R) × (κ → R)) (φ : (κ → R) → ℂ) :
    mulQ χ (⅟2) (-B) (schr χ w φ) = schr χ (w.1, B *ᵥ w.1 + w.2) (mulQ χ (⅟2) (-B) φ) := by
  have hB' : (-B)ᵀ = -B := by rw [Matrix.transpose_neg, hB]
  funext x
  have key := quad_add (-B) hB' x w.1 w.2
  rw [Matrix.neg_mulVec, neg_neg] at key
  simp only [mulQ_apply, schr]
  rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, key]

theorem act_unip {F R κ : Type} [Field F] [CommRing R] [Algebra F R] [Fintype κ] [DecidableEq κ] (b : Matrix κ κ F)
    (w : (κ → R) × (κ → R)) :
    act ((Matrix.fromBlocks 1 0 b 1 : Matrix (κ ⊕ κ) (κ ⊕ κ) F).map (algebraMap F R)) w =
      (w.1, b.map (algebraMap F R) *ᵥ w.1 + w.2) := by
  rw [Matrix.fromBlocks_map, Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_zero _ (map_zero _), act_fromBlocks]
  simp only [Matrix.one_mulVec, Matrix.zero_mulVec, add_zero]

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def qI (F : Type) [Field F] [NumberField F] : AF F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (RingHom.fst _ _)

theorem eventually_integral (x : κ → AF F) :
    ∀ᶠ v : Pl F in cofinite, ∀ i, evFin F v (x i) ∈ v.adicCompletionIntegers F :=
  eventually_all.2 fun i => (x i).2.2

theorem finite_mulSupport {φ : ∀ v : Pl F, (κ → Fv F v) → ℂ} (hφ : IsFam φ) (x : κ → AF F) :
    (Function.mulSupport fun v : Pl F => φ v fun i => evFin F v (x i)).Finite := by
  refine (Filter.eventually_cofinite.1 (hφ.2.and (eventually_integral x))).subset fun v hv => ?_
  intro h
  apply hv
  change φ v _ = 1
  rw [h.1, ind, Set.indicator_of_mem (show (fun i => evFin F v (x i)) ∈ {x | ∀ i, x i ∈ v.adicCompletionIntegers F}
    from h.2), Pi.one_apply]

end GlobalTheory.RatWeilUnip

namespace GlobalTheory.RatWeilUnip

open GlobalTheory.AdelicSvNQuad (quad map_quad quad_neg quad_add continuous_quad archMul archMul_temperate)

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem mulQ_mem_SB {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] [NonarchimedeanAddGroup K]
    (χ : AddChar K ℂ) (hχ : Continuous χ) (h : K) (A : Matrix κ κ K) {φ : (κ → K) → ℂ} (hφ : φ ∈ SB (κ → K)) :
    mulQ χ h A φ ∈ SB (κ → K) :=
  ⟨((GlobalTheory.SchrSBFin.isLocallyConstant_addChar χ hχ).comp_continuous (continuous_quad h A)).mul hφ.1, hφ.2.mul_left⟩

theorem mulQ_bijOn {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] [NonarchimedeanAddGroup K]
    (χ : AddChar K ℂ) (hχ : Continuous χ) (h : K) (A : Matrix κ κ K) :
    Set.BijOn (mulQ χ h A) (SB (κ → K) : Set _) (SB (κ → K) : Set _) := by
  refine Set.InvOn.bijOn (f' := mulQ χ h (-A)) ⟨fun φ _ => mulQ_neg_mulQ χ h A φ, fun φ _ => ?_⟩
    (fun φ hφ => mulQ_mem_SB χ hχ h A hφ) (fun φ hφ => mulQ_mem_SB χ hχ h (-A) hφ)
  have := mulQ_neg_mulQ χ h (-A) φ
  rwa [neg_neg] at this

theorem quad_mem {v : Pl F} {h : Fv F v} (hh : h ∈ v.adicCompletionIntegers F) {A : Matrix κ κ (Fv F v)}
    (hA : ∀ i j, A i j ∈ v.adicCompletionIntegers F) {x : κ → Fv F v} (hx : ∀ i, x i ∈ v.adicCompletionIntegers F) :
    quad h A x ∈ v.adicCompletionIntegers F := by
  unfold quad
  refine mul_mem hh (sum_mem fun i _ => mul_mem (hx i) (sum_mem fun j _ => mul_mem (hA i j) (hx j)))

theorem invOf_two_eq (v : Pl F) : ⅟(2 : Fv F v) = algebraMap F (Fv F v) (2⁻¹) := by
  refine (invOf_eq_right_inv ?_)
  rw [← map_ofNat (algebraMap F (Fv F v)) 2, ← map_mul, mul_inv_cancel₀ two_ne_zero, map_one]

theorem eventually_mulQ_ind (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) (b : Matrix κ κ F) :
    ∀ᶠ v : Pl F in cofinite, mulQ (GlobalTheory.LatVac.psiAt ψ v) (⅟2) (-(b.map (algebraMap F (Fv F v)))) (ind κ v) = ind κ v := by
  filter_upwards [GlobalTheory.psiLoc_eventually_trivial_integers ψ hψ, eventually_algebraMap_mem_integers (2⁻¹ : F),
    eventually_all.2 fun i => eventually_all.2 fun j => eventually_algebraMap_mem_integers (b i j)] with v h1 h2 h3
  funext x
  rw [mulQ_apply]
  by_cases hx : ∀ i, x i ∈ v.adicCompletionIntegers F
  · have hq : quad (⅟2) (-(b.map (algebraMap F (Fv F v)))) x ∈ v.adicCompletionIntegers F :=
      quad_mem (show ⅟(2 : Fv F v) ∈ v.adicCompletionIntegers F by rw [invOf_two_eq]; exact h2) (fun i j => neg_mem (h3 i j)) hx
    rw [GlobalTheory.LatVac.psiAt_apply, h1 _ hq, one_mul]
  · rw [ind, Set.indicator_of_notMem (show x ∉ {x | ∀ i, x i ∈ v.adicCompletionIntegers F} from hx), mul_zero]

end GlobalTheory.RatWeilUnip

namespace GlobalTheory.RatWeilUnip

open GlobalTheory.AdelicSvNQuad (quad map_quad quad_neg quad_add continuous_quad archMul archMul_temperate)

open scoped Classical

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem invOf_two_eq' (R : Type) [CommRing R] [Algebra F R] [Invertible (2 : R)] : ⅟(2 : R) = algebraMap F R (2⁻¹) := by
  refine (invOf_eq_right_inv ?_)
  rw [← map_ofNat (algebraMap F R) 2, ← map_mul, mul_inv_cancel₀ two_ne_zero, map_one]

theorem evFin_quad (b : Matrix κ κ F) (v : Pl F) (x : κ → AF F) :
    evFin F v (quad (⅟2) (-(b.map (algebraMap F (AF F)))) x) =
      quad (⅟2) (-(b.map (algebraMap F (Fv F v)))) (fun i => evFin F v (x i)) := by
  simp [quad, dotProduct, Matrix.mulVec, map_sum, GlobalTheory.VacAny.evFin_invOf_two]

theorem psi_quad_rat (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (b : Matrix κ κ F) (ξ : κ → F) :
    ψ (quad (⅟2) (-(b.map (algebraMap F (AF F)))) (fun i => algebraMap F (AF F) (ξ i))) = 1 := by
  have h := map_quad (algebraMap F (AF F)) (2⁻¹ : F) (-b) ξ
  rw [Matrix.map_neg _ (map_neg _), ← invOf_two_eq'] at h
  rw [← h]
  exact hψ.2.1 _

theorem thetaSum_mulQ (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (b : Matrix κ κ F) (Φ : (κ → AF F) → ℂ) :
    thetaSum F (mulQ ψ (⅟2) (-(b.map (algebraMap F (AF F)))) Φ) = thetaSum F Φ := by
  unfold thetaSum
  congr 1
  funext ξ
  rw [mulQ_apply, psi_quad_rat ψ hψ b ξ, one_mul]

theorem archMul_neg_mul (h : mixedEmbedding.mixedSpace F) (A : Matrix κ κ (mixedEmbedding.mixedSpace F))
    (y : κ → mixedEmbedding.mixedSpace F) : archMul h A y * archMul h (-A) y = 1 := by
  unfold archMul
  rw [← AddChar.map_add_eq_mul, quad_neg, map_neg, neg_neg, neg_add_cancel, AddChar.map_zero_eq_one]

theorem surjective_arch (h : mixedEmbedding.mixedSpace F) (A : Matrix κ κ (mixedEmbedding.mixedSpace F)) :
    Function.Surjective (SchwartzMap.smulLeftCLM ℂ (archMul h A) : SInf F κ →L[ℂ] SInf F κ) := by
  intro f
  refine ⟨SchwartzMap.smulLeftCLM ℂ (archMul h (-A)) f, ?_⟩
  ext y
  rw [SchwartzMap.smulLeftCLM_apply_apply (archMul_temperate _ _),
    SchwartzMap.smulLeftCLM_apply_apply (archMul_temperate _ _), smul_eq_mul, smul_eq_mul, ← mul_assoc,
    archMul_neg_mul, one_mul]

theorem at_pairA (a : AF F) : At (evI F) (pairA F (fstA F a) 0) := by
  intro u hu
  have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (hu.trans (map_zero _).symm)
  refine Prod.ext ?_ ?_
  · change u.1 * _ = 0
    rw [h1, zero_mul]
  · change u.2 * 0 = 0
    exact mul_zero _

theorem mulQ_pure (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (b : Matrix κ κ F) (f : SInf F κ)
    {φ : ∀ v : Pl F, (κ → Fv F v) → ℂ} (hφ : IsFam φ) :
    mulQ ψ (⅟2) (-(b.map (algebraMap F (AF F)))) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (SchwartzMap.smulLeftCLM ℂ
                   (archMul (qI F (⅟2)) ((-(b.map (algebraMap F (AF F)))).map (qI F))) f)
        (fun v => mulQ (GlobalTheory.LatVac.psiAt ψ v) (⅟2) (-(b.map (algebraMap F (Fv F v)))) (φ v)) := by
  funext x
  set Q := quad (⅟2) (-(b.map (algebraMap F (AF F)))) x with hQ
  obtain ⟨hfin, hprod⟩ := GlobalTheory.T.adelicAddChar_eq_archimedean_mul_finprod_local F ψ hψ.1 Q
  simp only [hQ, evFin_quad] at hfin hprod
  have harch : ψ (pairA F (fstA F Q) 0) =
      archMul (qI F (⅟2)) ((-(b.map (algebraMap F (AF F)))).map (qI F)) (fun i => evI F (x i)) := by
    rw [hψ.2.2 _ (at_pairA Q)]
    have e1 : evI F (pairA F (fstA F Q) 0) =
        quad (qI F (⅟2)) ((-(b.map (algebraMap F (AF F)))).map (qI F)) (fun i => evI F (x i)) :=
      map_quad (qI F) _ _ x
    rw [e1, archMul, GlobalTheory.Published.Metaplectic.eChar_apply]
    congr 1
    push_cast
    ring
  rw [← hQ] at hprod
  change ψ Q * (f (fun i => evI F (x i)) * ∏ᶠ v, φ v fun i => evFin F v (x i)) =
    (SchwartzMap.smulLeftCLM ℂ (archMul (qI F (⅟2)) ((-(b.map (algebraMap F (AF F)))).map (qI F))) f)
      (fun i => evI F (x i)) * ∏ᶠ v, (GlobalTheory.LatVac.psiAt ψ v (quad (⅟2) (-(b.map (algebraMap F (Fv F v))))
        (fun i => evFin F v (x i))) * φ v fun i => evFin F v (x i))
  rw [finprod_mul_distrib hfin (finite_mulSupport hφ x), SchwartzMap.smulLeftCLM_apply_apply (archMul_temperate _ _),
    smul_eq_mul, hprod, harch]
  ring

end GlobalTheory.RatWeilUnip

namespace GlobalTheory.RatWeilUnip

open GlobalTheory.AdelicSvNQuad (quad archMul)

open scoped Classical in

theorem hasOp_unip : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    [DecidableEq κ] (b : Matrix κ κ F), bᵀ = b → HasOp ψ (Matrix.fromBlocks 1 0 b 1) := by
  intro F _ _ ψ hψ κ _ _ b hb
  have hB : ∀ (R : Type) [CommRing R] [Algebra F R], (b.map (algebraMap F R))ᵀ = b.map (algebraMap F R) :=
    fun R _ _ => by rw [← Matrix.transpose_map, hb]
  refine ⟨mulQ ψ (⅟2) (-(b.map (algebraMap F (AF F)))), 1,
    SchwartzMap.smulLeftCLM ℂ (archMul (qI F (⅟2)) ((-(b.map (algebraMap F (AF F)))).map (qI F))),
    fun v => mulQ (GlobalTheory.LatVac.psiAt ψ v) (⅟2) (-(b.map (algebraMap F (Fv F v)))), one_ne_zero,
    surjective_arch _ _, fun v => mulQ_bijOn _ (GlobalTheory.VacAny.continuous_psiV hψ.1 v) _ _, fun v w φ _ => ?_,
    eventually_mulQ_ind ψ hψ.1 b, fun f φ hφ => ⟨mulQ_pure ψ hψ b f hφ, fun w => ?_, ?_⟩⟩
  · rw [act_unip, mulQ_schr _ _ (hB _)]
  · rw [act_unip, mulQ_schr _ _ (hB _)]
  · rw [thetaSum_mulQ ψ hψ b, one_mul]

end GlobalTheory.RatWeilUnip

end
end

open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowerUnipotent_hasRationalWeilOperator_quadraticChar : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (b : Matrix κ κ F), bᵀ = b →
    HasOp ψ (Matrix.fromBlocks 1 0 b 1) := by
  atlas_forward_decl GlobalTheory.RatWeilUnip.hasOp_unip
end

section
open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weylElement_hasRationalWeilOperator_adelicFourier : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ] [DecidableEq κ],
    HasOp ψ (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (κ ⊕ κ) (κ ⊕ κ) F) := by
  first | exact @GlobalTheory.WeylFourier.weyl_hasOp | exact GlobalTheory.WeylFourier.weyl_hasOp | (intros; apply GlobalTheory.WeylFourier.weyl_hasOp <;> assumption)
end

section
noncomputable section

namespace GlobalTheory.RatWeilOp

open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F : Type} [Field F] [NumberField F]

theorem hasOp_of_symplectic (hF : IsTotallyReal F) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {κ : Type} [Fintype κ] [DecidableEq κ]
    (a : Matrix (κ ⊕ κ) (κ ⊕ κ) F) (ha : aᵀ * Matrix.fromBlocks 0 1 (-1) 0 * a = Matrix.fromBlocks 0 1 (-1) 0) : HasOp ψ a :=
  GlobalTheory.T.symplecticGroup_generated_levi_lowerUnipotent_weyl F κ (HasOp ψ) (fun _ _ => HasOp.mul) (GlobalTheory.T.hasRationalWeilOperator_leviBlock F ψ κ) (GlobalTheory.T.lowerUnipotent_hasRationalWeilOperator_quadraticChar F ψ hψ κ) (GlobalTheory.T.weylElement_hasRationalWeilOperator_adelicFourier F hF ψ hψ κ) a ha

section Pure

variable {κ : Type} [Fintype κ]

theorem pure_mem (f : SInf F κ) {φ : ∀ v : Pl F, (κ → Fv F v) → ℂ} (hφ : IsFam φ) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∈ schA F κ :=
  Submodule.subset_span ⟨f, fun y => ∏ᶠ v, φ v fun i => evalV F v (y i),
    ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV φ hφ.1 hφ.2, GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod φ hφ.1 hφ.2⟩, rfl⟩

theorem schA_le {N : Submodule ℂ ((κ → AF F) → ℂ)} (h : ∀ f φ, IsFam φ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∈ N) : schA F κ ≤ N := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, g, hg, rfl⟩
  replace hg := GlobalTheory.T.schwartzBruhat_finiteAdeles_mem_span_restrictedProducts F _ g hg
  induction hg using Submodule.span_induction with
  | zero => rw [show pureA F f 0 = 0 from funext fun _ => mul_zero _]; exact N.zero_mem
  | add a b _ _ ha hb =>
    rw [show pureA F f (a + b) = pureA F f a + pureA F f b from funext fun _ => mul_add _ _ _]; exact N.add_mem ha hb
  | smul c a _ ha =>
    rw [show pureA F f (c • a) = c • pureA F f a from funext fun _ => mul_left_comm _ _ _]; exact N.smul_mem c ha
  | mem p hp =>
    obtain ⟨φ, hφ, hs, rfl⟩ := hp
    exact h f φ ⟨hφ, hs⟩

theorem IsFam.finite {φ : ∀ v : Pl F, (κ → Fv F v) → ℂ} (hφ : IsFam φ) (x : κ → AF F) :
    (Function.mulSupport fun v => φ v fun i => evFin F v (x i)).Finite := by
  have h : ∀ᶠ v in cofinite, ∀ i, evFin F v (x i) ∈ v.adicCompletionIntegers F := eventually_all.2 fun i => (x i).2.2
  refine (eventually_cofinite.1 ?_)
  filter_upwards [h, hφ.2] with v h1 h2
  rw [h2, ind, Set.indicator_of_mem (show _ ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from h1)]
  rfl

theorem pure_smul (f : SInf F κ) {φ : ∀ v : Pl F, (κ → Fv F v) → ℂ} (hφ : IsFam φ) (m : Pl F → ℂ) (h0 : ∀ v, m v ≠ 0)
    (h1 : ∀ᶠ v in cofinite, m v = 1) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure ((∏ᶠ v, m v) • f) (fun v => (m v)⁻¹ • φ v) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ := by
  funext x
  have hm : (Function.mulSupport m).Finite := eventually_cofinite.1 h1
  have hm' : (Function.mulSupport fun v => (m v)⁻¹).Finite := hm.subset fun v hv h => hv (by simp only [h, inv_one])
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Pi.smul_apply, smul_eq_mul, SchwartzMap.smul_apply]
  rw [finprod_mul_distrib hm' (hφ.finite x)]
  have : (∏ᶠ v, m v) * ∏ᶠ v, (m v)⁻¹ = 1 := by
    rw [← finprod_mul_distrib hm hm']
    exact finprod_eq_one_of_forall_eq_one fun v => mul_inv_cancel₀ (h0 v)
  linear_combination (f (fun i => evI F (x i)) * ∏ᶠ v, φ v fun i => evFin F v (x i)) * this

def schrL {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) (w : (κ → R) × (κ → R)) :
    ((κ → R) → ℂ) →ₗ[ℂ] (κ → R) → ℂ where
  toFun := schr ψ w
  map_add' φ φ' := funext fun x => by simp only [schr, Pi.add_apply]; ring
  map_smul' a φ := funext fun x => by simp only [schr, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

variable {ψ : AddChar (AF F) ℂ} {a : Matrix (κ ⊕ κ) (κ ⊕ κ) F} {e : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ → AF F) → ℂ} {c : ℂ}
  {ei : SInf F κ →L[ℂ] SInf F κ} {ev : ∀ v : Pl F, ((κ → Fv F v) → ℂ) →ₗ[ℂ] (κ → Fv F v) → ℂ}

theorem IsOp.maps (h : IsOp ψ a e c ei ev) : ∀ Φ ∈ schA F κ, e Φ ∈ schA F κ := fun _ hΦ =>
  schA_le (N := (schA F κ).comap e) (fun f φ hφ => by
    rw [Submodule.mem_comap, (h.2.2.2.2.2 f φ hφ).1]
    exact pure_mem _ (h.isFam hφ)) hΦ

theorem IsOp.Heisenberg₂ (h : IsOp ψ a e c ei ev) (w : (κ → AF F) × (κ → AF F)) :
    ∀ Φ ∈ schA F κ, e (schr ψ w Φ) = schr ψ (act (a.map (algebraMap F (AF F))) w) (e Φ) := fun _ hΦ =>
  schA_le (N := LinearMap.eqLocus (e ∘ₗ schrL ψ w) (schrL ψ (act (a.map (algebraMap F (AF F))) w) ∘ₗ e))
    (fun f φ hφ => (h.2.2.2.2.2 f φ hφ).2.1 w) hΦ

theorem IsOp.theta (h : IsOp ψ a e c ei ev) : ∀ Φ ∈ schA F κ, thetaSum F (e Φ) = c * thetaSum F Φ := fun _ hΦ =>
  (schA_le (N := {
      carrier := {Φ | Φ ∈ schA F κ ∧ thetaSum F (e Φ) = c * thetaSum F Φ}
      zero_mem' := ⟨zero_mem _, by simp [thetaSum]⟩
      add_mem' := fun {x y} hx hy => ⟨add_mem hx.1 hy.1, by
        rw [map_add, thetaSum_add F (h.maps _ hx.1) (h.maps _ hy.1), thetaSum_add F hx.1 hy.1, hx.2, hy.2, mul_add]⟩
      smul_mem' := fun r x hx => ⟨Submodule.smul_mem _ r hx.1, by
        rw [map_smul, thetaSum_smul, thetaSum_smul, hx.2, mul_left_comm]⟩ })
    (fun f φ hφ => ⟨pure_mem f hφ, (h.2.2.2.2.2 f φ hφ).2.2⟩) hΦ).2

theorem IsOp.bijOn (hψ : IsStd ψ) (h : IsOp ψ a e c ei ev) : Set.BijOn e (schA F κ : Set _) (schA F κ : Set _) := by
  classical
  refine ⟨h.maps, fun Φ hΦ Φ' hΦ' he => ?_, ?_⟩
  · have hd : Φ - Φ' ∈ schA F κ := sub_mem hΦ hΦ'
    refine sub_eq_zero.1 (GlobalTheory.T.eq_zero_of_schroedingerTranslates_thetaSum_zero F ψ hψ κ _ hd fun w => ?_)
    have h1 := h.theta _ (GlobalTheory.HeisSchA.schr_mem_schA ψ hψ w _ hd)
    rw [h.Heisenberg₂ w _ hd, map_sub, he, sub_self, show schr ψ _ (0 : (κ → AF F) → ℂ) = 0 from (schrL ψ _).map_zero] at h1
    exact (mul_eq_zero.1 (h1.symm.trans (by simp [thetaSum]))).resolve_left h.1
  · refine schA_le (N := (schA F κ).map e) fun g φ' hφ' => ?_
    obtain ⟨f, rfl⟩ := h.2.1 g
    have key : ∀ v, ∃ p ∈ SB (κ → Fv F v), ev v p = φ' v ∧ (φ' v = ind κ v → ev v (ind κ v) = ind κ v → p = ind κ v) := by
      intro v
      by_cases hv : φ' v = ind κ v ∧ ev v (ind κ v) = ind κ v
      · exact ⟨ind κ v, hv.1 ▸ hφ'.1 v, hv.2.trans hv.1.symm, fun _ _ => rfl⟩
      · obtain ⟨p, hp, hp'⟩ := (h.2.2.1 v).surjOn (hφ'.1 v)
        exact ⟨p, hp, hp', fun h1 h2 => absurd ⟨h1, h2⟩ hv⟩
    choose φ h1 h2 h3 using key
    have hφ : IsFam φ := ⟨h1, by filter_upwards [hφ'.2, h.2.2.2.2.1] with v p q using h3 v p q⟩
    exact ⟨_, pure_mem f hφ, by rw [(h.2.2.2.2.2 f φ hφ).1]; simp only [h2]⟩

end Pure

section Vac

variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

theorem schr_of_acts (M : Model σ X W) (ψ : AddChar (AF F) ℂ) {v : Pl F} {γ : Matrix (Fin n) (Fin d) (AE F E)} (hγ : γ ∈ latAtV X W v)
    {φ : (Fin n × Fin d → Fv F v) → ℂ} (hφ : φ ∈ SB _) {χ : ℂ} (h : Acts (evFin F v) (M.co.rho ψ γ) φ (χ • φ)) :
    schr (GlobalTheory.LatVac.psiAt ψ v) (GlobalTheory.LatVac.locCo M.co v γ) φ = χ • φ := by
  obtain ⟨r, hr, x₀, hx₀⟩ := GlobalTheory.RestComplement.exists_rest_ne_zero v φ hφ
  funext ξ
  have := GlobalTheory.LatVac.heis_at_local_identity v M.co ψ γ φ χ ((GlobalTheory.LatVac.latAtV_at_stable X W v).1 γ hγ) h r hr x₀ hx₀ ξ
  rw [schr, invOf_eq_inv]
  exact this

theorem vac_line (B : Base F E) {r s r' s' : ℕ} (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s')
    (M : Model σ X W) (v : Pl F) {φ φ' : (Fin n × Fin d → Fv F v) → ℂ} (h : M.IsVac B.ψ v φ) (h' : M.IsVac B.ψ v φ') :
    ∃ m : ℂ, φ' = m • φ := by
  classical
  obtain ⟨hφ, hφ0, θ, hθ, hA⟩ := h
  obtain ⟨hφ', -, θ', hθ', hA'⟩ := h'
  have hAt := (GlobalTheory.LatVac.latAtV_at_stable X W v).1
  let χ : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v) → ℂ := fun l =>
    if h : ∃ γ ∈ latAtV X W v, GlobalTheory.LatVac.locCo M.co v γ = l then
      B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F W.J) h.choose h.choose) else 0
  have loc : ∀ f : (Fin n × Fin d → Fv F v) → ℂ, f ∈ SB _ →
      (∀ γ ∈ latAtV X W v, Acts (evFin F v) (M.co.rho B.ψ γ) f
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F W.J) γ γ) • f)) →
      ∀ l ∈ (latAtV X W v).map (GlobalTheory.LatVac.locCo M.co v), ∀ ξ,
        GlobalTheory.LatVac.psiAt B.ψ v (ξ ⬝ᵥ l.2 + (2 : Fv F v)⁻¹ * (l.1 ⬝ᵥ l.2)) * f (ξ + l.1) = χ l * f ξ := by
    intro f hf hA l hl ξ
    have h : ∃ γ ∈ latAtV X W v, GlobalTheory.LatVac.locCo M.co v γ = l := AddSubgroup.mem_map.mp hl
    have key := congrFun (schr_of_acts M B.ψ h.choose_spec.1 hf (hA _ h.choose_spec.1)) ξ
    simp only [χ, dif_pos h]
    rw [h.choose_spec.2, schr, invOf_eq_inv] at key
    exact key
  obtain ⟨c, hc0, hcb⟩ := GlobalTheory.LatBound.locCo_latAtV_bounded X W v M.co hX.lat hW.lat
  have hsd := GlobalTheory.LatVac.DualLoc.map_selfDual v M.co B.ψ _ hAt (GlobalTheory.T.heisenbergLattice_selfDual_every_finitePlace F E σ B n d X W r s r' s' hB hX hW v)
  have hfill := GlobalTheory.T.self_dual_lattice_invariant_vector F v _ (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.VacAny.continuous_psiV hB.std.1 v)
    (fun _ => GlobalTheory.StdCharFromIsStd.norm_psi hB.std _) (GlobalTheory.PsiNontriv.psiAt_ne_one B.ψ hB.std v) _ c hc0 hsd
    (fun l hl i => by
      obtain ⟨γ, hγ, rfl⟩ := AddSubgroup.mem_map.mp hl
      exact hcb γ hγ i)
  refine GlobalTheory.heisenbergEigen_proportional (GlobalTheory.LatVac.psiAt B.ψ v) _ χ φ φ' (loc φ hφ hA) (loc φ' hφ' fun γ hγ => ?_) hφ0 hfill
  rw [GlobalTheory.T.vacuum_eigenvalue_theta_independent F E σ B n d X W r s r' s' hB hX hW v θ θ' hθ hθ' γ hγ]
  exact hA' γ hγ

theorem IsOp.isVac {ψ : AddChar (AF F) ℂ} {a e c ei ev} (h : IsOp (κ := Fin n × Fin d) ψ a e c ei ev) (M M₁ : Model σ X W)
    (hco : ∀ u, M₁.co.e u = act (a.map (algebraMap F (AF F))) (M.co.e u)) (v : Pl F) {φ : (Fin n × Fin d → Fv F v) → ℂ}
    (hφ : M.IsVac ψ v φ) : M₁.IsVac ψ v (ev v φ) := by
  obtain ⟨h1, h0, θ, hθ, hA⟩ := hφ
  refine ⟨(h.2.2.1 v).mapsTo h1, fun h2 => h0 ((h.2.2.1 v).injOn h1 (zero_mem _) (h2.trans (map_zero _).symm)), θ, hθ,
    fun γ hγ => ?_⟩
  have e1 : GlobalTheory.LatVac.locCo M₁.co v γ = act (a.map (algebraMap F (Fv F v))) (GlobalTheory.LatVac.locCo M.co v γ) := by
    have e2 : ∀ k, evFin F v ((a.map (algebraMap F (AF F)) *ᵥ Sum.elim (M.co.e γ).1 (M.co.e γ).2) k) =
        (a.map (algebraMap F (Fv F v)) *ᵥ Sum.elim (GlobalTheory.LatVac.locCo M.co v γ).1 (GlobalTheory.LatVac.locCo M.co v γ).2) k := fun k => by
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, AlgHom.commutes]
      refine Finset.sum_congr rfl fun j _ => ?_
      cases j <;> rfl
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
    · show evFin F v ((M₁.co.e γ).1 k) = _
      rw [hco]; exact e2 _
    · show evFin F v ((M₁.co.e γ).2 k) = _
      rw [hco]; exact e2 _
  have e3 := GlobalTheory.VacBridge.rho_acts_locCo M₁.co ψ v γ ((GlobalTheory.LatVac.latAtV_at_stable X W v).1 γ hγ) (ev v φ)
  rwa [e1, ← h.2.2.2.1 v _ φ h1, schr_of_acts M ψ hγ h1 (hA γ hγ), map_smul] at e3

end Vac

theorem exists_intertwiner : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M M₁ : Model σ X W) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ → M₁.IsGood B.ψ → ∀ a : Matrix ((Fin n × Fin d) ⊕ (Fin n × Fin d)) ((Fin n × Fin d) ⊕ (Fin n × Fin d)) F, aᵀ * Matrix.fromBlocks 0 1 (-1) 0 * a = Matrix.fromBlocks 0 1 (-1) 0 → (∀ u, M₁.co.e u = ((a.map (algebraMap F (AF F)) *ᵥ Sum.elim (M.co.e u).1 (M.co.e u).2) ∘ Sum.inl, (a.map (algebraMap F (AF F)) *ᵥ Sum.elim (M.co.e u).1 (M.co.e u).2) ∘ Sum.inr)) → ∃ (e : Fn F n d →ₗ[ℂ] Fn F n d) (c : ℂ), c ≠ 0 ∧ IsEv B M M₁ 1 1 ∅ e ∧ Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) ∧ ∀ Φ ∈ schA F (Fin n × Fin d), thetaSum F (e Φ) = c * thetaSum F Φ := by
  intro _ F E _ _ _ _ _ σ B n d X W M M₁ r s r' s' hB hX hW hM hM₁ a ha hco
  obtain ⟨e, c, ei, ev, h⟩ := hasOp_of_symplectic hB.cm.1 hB.std a ha
  have key : ∀ v, ∃ m : ℂ, m ≠ 0 ∧ ev v (M.vac v) = m • M₁.vac v ∧ (ev v (M.vac v) = M₁.vac v → m = 1) := fun v => by
    by_cases hv : ev v (M.vac v) = M₁.vac v
    · exact ⟨1, one_ne_zero, by rw [hv, one_smul], fun _ => rfl⟩
    · have h1 := h.isVac M M₁ hco v (hM.vac v)
      obtain ⟨m, hm⟩ := vac_line B hB hX hW M₁ v (hM₁.vac v) h1
      exact ⟨m, fun h0 => h1.2.1 (by rw [hm, h0, zero_smul]), hm, fun h2 => absurd h2 hv⟩
  choose m hm0 hm hm1 using key
  have hmc : ∀ᶠ v in cofinite, m v = 1 := by
    filter_upwards [hM.std, hM₁.std, h.2.2.2.2.1] with v h1 h2 h3
    exact hm1 v (by rw [h1, h2]; exact h3)
  have hP : (∏ᶠ v, m v) ≠ 0 := finprod_induction (fun z : ℂ => z ≠ 0) one_ne_zero (fun _ _ => mul_ne_zero) hm0
  refine ⟨e, c, h.1, ⟨h.maps, fun z Φ hΦ => ?_, fun u hu => absurd hu (Set.notMem_empty u),
    (∏ᶠ v, m v) • ei, fun v => (m v)⁻¹ • ev v, fun h0 => ?_, fun v => ⟨?_, ?_⟩, fun f φ h1 h2 => ?_⟩, h.bijOn hB.std, h.theta⟩
  · have h1 : ∀ k : ℕ, incM F (1 : Matrix (Fin k) (Fin k) E) = 1 := fun k => Matrix.map_one _ (map_zero _) (map_one _)
    rw [h1, h1, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one, Darboux.rho, Darboux.rho, hco]
    exact h.Heisenberg₂ _ Φ hΦ
  · have h1 : ei = 0 := (smul_eq_zero.1 h0).resolve_left hP
    obtain ⟨Φ, hΦ, hΦ0⟩ := GlobalTheory.SchANonzero.exists_mem_schA_ne_zero F (Fin n × Fin d)
    have h2 : schA F (Fin n × Fin d) ≤ ⊥ := schA_le fun g φ _ => by
      obtain ⟨f, rfl⟩ := h.2.1 g
      rw [h1, Submodule.mem_bot]
      funext x
      simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
    exact hΦ0 (by rw [(Submodule.mem_bot ℂ).1 (h2 hΦ)]; rfl)
  · rw [LinearMap.smul_apply, hm, smul_smul, inv_mul_cancel₀ (hm0 v), one_smul]
  · rw [Submodule.map_smul _ _ _ (inv_ne_zero (hm0 v))]
    exact SetLike.coe_injective ((Submodule.map_coe _ _).trans (h.2.2.1 v).image_eq)
  · have hφ : IsFam φ := ⟨h1, by filter_upwards [h2, hM.std] with v p q using p.trans q⟩
    rw [(h.2.2.2.2.2 f φ hφ).1, ← pure_smul (ei f) (h.isFam hφ) m hm0 hmc]
    rfl

end GlobalTheory.RatWeilOp

end
end
