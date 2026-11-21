import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsCompactLatticeStabilizerBoundedReal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompMemGinfC
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LatHatOpenAndContinuous
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RealAdelesCmFieldEquivComplexCmType
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ArchimedeanMatrixUnitaryContinuousMultiplicative

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.Mem.Th GlobalTheory.Cusp
open Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Cusp.KinfCompact

section Mat

variable {p q n : ℕ} {A : Matrix (Fin p ⊕ Fin q) (Fin n) ℂ} {B : Matrix (Fin n) (Fin p ⊕ Fin q) ℂ}
  {G m : Matrix (Fin n) (Fin n) ℂ}

theorem Jpq_mul_self : Formalism.UG.Jpq p q * Formalism.UG.Jpq p q = 1 := by
  simp [Formalism.UG.Jpq, Matrix.fromBlocks_multiply]

theorem inv_frame (hA : Aᴴ * Formalism.UG.Jpq p q * A = G) (h : A * B = 1) : Bᴴ * G * B = Formalism.UG.Jpq p q := by
  calc Bᴴ * G * B = (A * B)ᴴ * Formalism.UG.Jpq p q * (A * B) := by
        rw [← hA, conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [h, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]


theorem norm_entry_le (hA : Aᴴ * Formalism.UG.Jpq p q * A = G) (h1 : B * A = 1) (h2 : A * B = 1) (hm : mᴴ * G * m = G)
    (h : Formalism.UG.Jpq p q * (A * m * B) = A * m * B * Formalism.UG.Jpq p q) (i j : Fin n) :
    ‖m i j‖ ≤ ∑ c, ∑ a, ‖B i a‖ * ‖A c j‖ := by
  set b := A * m * B with hb
  have e1 : bᴴ * Formalism.UG.Jpq p q * b = Formalism.UG.Jpq p q := by
    calc _ = Bᴴ * (mᴴ * (Aᴴ * Formalism.UG.Jpq p q * A) * m) * B := by
          rw [hb, conjTranspose_mul, conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hA, hm, inv_frame hA h2]
  have e2 : bᴴ * b = 1 := by
    rw [Matrix.mul_assoc, h, ← Matrix.mul_assoc] at e1
    rw [← Matrix.mul_one (bᴴ * b), ← Jpq_mul_self, ← Matrix.mul_assoc, e1]
  have hU : b ∈ Matrix.unitaryGroup (Fin p ⊕ Fin q) ℂ := Matrix.mem_unitaryGroup_iff'.2 e2
  have e3 : m = B * b * A := by
    rw [hb]; simp only [← Matrix.mul_assoc, h1, Matrix.one_mul]
    rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  rw [e3, Matrix.mul_apply]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
  rw [norm_mul, ← Finset.sum_mul, Matrix.mul_apply]
  refine mul_le_mul_of_nonneg_right ((norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)) (norm_nonneg _)
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (entry_norm_bound_of_unitary hU a c)

end Mat

variable {D : D7}

theorem isClosed_realPts (V : HSp D) : IsClosed (GinfC V : Set (GA D V)) := by
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField D.host.F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := D.host.F) (E := D.host.E) (Af D.host.F)
  have : T2Space (Af D.host.F ⊗[D.host.F] D.host.E) := e.isEmbedding.t2Space
  have h : (GinfC V : Set (GA D V)) = {g | (finHom V g).1 = 1} := by
    ext g
    exact Units.ext_iff
  rw [h]
  exact isClosed_eq (GlobalTheory.Member.continuous_finHom_val D V) continuous_const

theorem continuous_realMat {θ : InfF D} (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau) :
    Continuous fun h => infMat D.sp.cm.sig V.gram (θ τ) h := by
  obtain ⟨θ₀, hθ₀⟩ := (GlobalTheory.Member.infiniteAdele_bijective D).1
  have e : θ τ = θ₀ (tauE D τ) := SmoothForms.RealPts.infEmb_unique _ _ _ (hθ τ) (hθ₀ _)
  rw [e]
  exact ((GlobalTheory.Member.Arch.archM_spec D V θ₀ hθ₀).1 (tauE D τ)).2.2.2.1


end GlobalTheory.Cusp.KinfCompact

end
