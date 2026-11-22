module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.LeviOp

variable {F : Type} [Field F] {κ : Type} [Fintype κ] [DecidableEq κ]

theorem map_inv_mul {S : Type} [CommRing S] (g : F →+* S) (A : Matrix κ κ F) (h : IsUnit A.det) :
    A⁻¹.map g * A.map g = 1 := by
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul A h, Matrix.map_one g (map_zero g) (map_one g)]

theorem map_mul_inv {S : Type} [CommRing S] (g : F →+* S) (A : Matrix κ κ F) (h : IsUnit A.det) :
    A.map g * A⁻¹.map g = 1 := by
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv A h, Matrix.map_one g (map_zero g) (map_one g)]

theorem hom_mulVec {S T : Type} [CommRing S] [CommRing T] (f : S →+* T) (g : F →+* S) (g' : F →+* T)
    (hg : f.comp g = g') (M : Matrix κ κ F) (x : κ → S) (i : κ) :
    f ((M.map g *ᵥ x) i) = (M.map g' *ᵥ (fun j => f (x j))) i := by
  subst hg
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

def homeo {S : Type} [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] (g : F →+* S) (A : Matrix κ κ F)
    (hA : IsUnit A.det) : (κ → S) ≃ₜ (κ → S) where
  toFun x := A⁻¹.map g *ᵥ x
  invFun x := A.map g *ᵥ x
  left_inv x := by simp only [Matrix.mulVec_mulVec, map_mul_inv g A hA, Matrix.one_mulVec]
  right_inv x := by simp only [Matrix.mulVec_mulVec, map_inv_mul g A hA, Matrix.one_mulVec]
  continuous_toFun := Continuous.matrix_mulVec continuous_const continuous_id
  continuous_invFun := Continuous.matrix_mulVec continuous_const continuous_id

def linEquiv {S : Type} [CommRing S] [Algebra ℝ S] [TopologicalSpace S] [IsTopologicalRing S] (g : F →+* S)
    (A : Matrix κ κ F) (hA : IsUnit A.det) : (κ → S) ≃L[ℝ] (κ → S) where
  toFun x := A⁻¹.map g *ᵥ x
  invFun x := A.map g *ᵥ x
  map_add' x y := Matrix.mulVec_add _ x y
  map_smul' c x := Matrix.mulVec_smul _ c x
  left_inv x := by simp only [Matrix.mulVec_mulVec, map_mul_inv g A hA, Matrix.one_mulVec]
  right_inv x := by simp only [Matrix.mulVec_mulVec, map_inv_mul g A hA, Matrix.one_mulVec]
  continuous_toFun := Continuous.matrix_mulVec continuous_const continuous_id
  continuous_invFun := Continuous.matrix_mulVec continuous_const continuous_id

theorem sb_comp {X : Type} [TopologicalSpace X] (h : X ≃ₜ X) {φ : X → ℂ} (hφ : φ ∈ SB X) : φ ∘ h ∈ SB X :=
  ⟨hφ.1.comp_continuous h.continuous, hφ.2.comp_homeomorph h⟩

variable [NumberField F]

def evIr : AF F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (RingHom.fst _ _)

end GlobalTheory.LeviOp
