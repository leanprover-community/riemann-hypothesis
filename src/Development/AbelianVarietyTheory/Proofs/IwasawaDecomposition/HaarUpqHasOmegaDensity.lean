import Mathlib
import Formalism.LocalRingCardinality.DataCD
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousMatExp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDensityOriginOfAlmostHomogeneous
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqExpLocalChart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqLocallyCompactGroup

section
open Formalism.BasicNotions MeasureTheory Filter Topology Matrix
open scoped ENNReal NNReal

noncomputable section

namespace GlobalTheory.OmegaLebExists

theorem J_conjTranspose (P Q : ℕ) : (Formalism.UG.Jpq P Q)ᴴ = Formalism.UG.Jpq P Q := by
  unfold Formalism.UG.Jpq
  rw [fromBlocks_conjTranspose]
  simp

def cplxMap (P Q : ℕ) :
    (lieU P Q × lieU P Q) →ₗ[ℝ] ((Fin P ⊕ Fin Q) × (Fin P ⊕ Fin Q) → ℂ) where
  toFun ab := entries ((ab.1 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) +
        Complex.I • (ab.2 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ))
  map_add' x y := by
    funext ij
    simp [entries]
    ring
  map_smul' c x := by
    funext ij
    simp [entries]
    ring

end GlobalTheory.OmegaLebExists
end
end

section
open Formalism.BasicNotions MeasureTheory Filter Topology Matrix

noncomputable section

namespace GlobalTheory.HaarDensityUpq

def toL1 (P Q : ℕ) : lieU P Q →ₗ[ℝ] PiLp 1 (fun _ : (Fin P ⊕ Fin Q) × (Fin P ⊕ Fin Q) => ℂ) where
  toFun X := WithLp.toLp 1 (entries (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem toL1_injective (P Q : ℕ) : Function.Injective (toL1 P Q) := by
  intro X Y h
  ext i j
  exact congrFun (congrArg WithLp.ofLp h) (i, j)

theorem isInducing_toL1 (P Q : ℕ) : IsInducing (toL1 P Q) := by
  have h1 : IsInducing (entries : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ → _) :=
    (Homeomorph.piCurry (X := Fin P ⊕ Fin Q) (Y := Fin P ⊕ Fin Q) (Z := ℂ)).symm.isInducing
  exact (PiLp.homeomorph 1 (fun _ : (Fin P ⊕ Fin Q) × (Fin P ⊕ Fin Q) => ℂ)).symm.isInducing.comp
    (h1.comp IsInducing.subtypeVal)

@[reducible] def sumNorm (P Q : ℕ) : NormedAddCommGroup (lieU P Q) :=
  let N := NormedAddCommGroup.induced (lieU P Q) _ (toL1 P Q) (toL1_injective P Q)
  { toNorm := N.toNorm
    toAddCommGroup := inferInstance
    toMetricSpace := N.toMetricSpace.replaceTopology (isInducing_toL1 P Q).eq_induced
    dist_eq := N.dist_eq }

theorem mat_mul {P Q : ℕ} (g h : UpqT P Q) : (g * h).mat = g.mat * h.mat := rfl

end GlobalTheory.HaarDensityUpq
end
end
