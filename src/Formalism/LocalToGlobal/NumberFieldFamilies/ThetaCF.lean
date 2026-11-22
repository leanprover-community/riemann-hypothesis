module

public import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCB
public import Formalism.SharpRestriction.InertJacobiLevels.ExtraTheta

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

namespace Formalism.L2.Fam.ThC

open Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gaps

variable (D : D7)

end Gaps

variable {D : D7}

theorem emb_star (τ : D.host.E →+* ℂ) (x : D.host.E) : τ (star x) = starRingEnd ℂ (τ x) := by
  exact @NumberField.IsCMField.complexEmbedding_complexConj D.host.E _ _ D.host.isCMField_hostE _ τ x

theorem gram_herm (V : HSp D) (τ : D.host.E →+* ℂ) : Formalism.UG.IsHerm (starRingEnd ℂ) (V.gram.map τ) := by
  unfold Formalism.UG.IsHerm Formalism.UG.cT
  ext i j
  simp only [Matrix.transpose_apply, Matrix.map_apply, HSpace.gram]
  rw [← emb_star]
  congr 1
  have := V.herm.eq (V.frame j) (V.frame i)
  rw [starRingEnd_apply] at this
  exact this

theorem sig_ex (V : HSp D) (τ : D.host.E →+* ℂ) : ∃ s : ℕ × ℕ, Formalism.UG.HasSignature (V.gram.map τ) s.1 s.2 := by
  obtain ⟨p, q, h⟩ := Formalism.UG.P.signature_exists _ (V.gram.map τ) (gram_herm V τ) (by
    have : (V.gram.map τ).det = τ V.gram.det := (τ.map_det V.gram).symm
    rw [this]
    exact ((map_ne_zero τ).2 (gram_det_ne V)).isUnit)
  exact ⟨(p, q), h⟩

open Classical in
def fixSig (V : HSp D) : HSp D := { V with sig := if V.SigOK then V.sig else fun τ => (sig_ex V τ).choose }

theorem fixSig_ok (V : HSp D) : (fixSig V).SigOK := by
  unfold HSpace.SigOK
  intro τ
  by_cases h : V.SigOK
  · simp only [fixSig, h, if_true]
    exact h τ
  · simp only [fixSig, h, if_false]
    exact (sig_ex V τ).choose_spec

end Formalism.L2.Fam.ThC

end
