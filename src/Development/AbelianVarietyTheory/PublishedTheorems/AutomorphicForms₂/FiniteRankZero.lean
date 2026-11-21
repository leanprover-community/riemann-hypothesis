import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot

noncomputable section

open NumberField GlobalTheory.CuspRep Formalism.L2.Host

namespace GlobalTheory.Published.AutFinGL.Model

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}




def kerL (a : ℕ) (χ : HChar E) : Subgroup (GL (Fin a) (Af E)) := ((chiDet a χ).comp (finGL E a)).ker

theorem isOpen_kerL (χ : HChar E) : IsOpen (kerL a χ : Set (GL (Fin a) (Af E))) := isOpen_ker_chiDet χ

def kRep (a : ℕ) (χ : HChar E) : Representation ℂ (Kinf E a) ℂ :=
  twRep (Representation.trivial ℂ (Kinf E a) ℂ) ((chiDet a χ).comp ((infGL E a).comp Unitary.toUnits))

theorem isContRep_kRep (χ : HChar E) : AutFin.IsContRep (kRep a χ) := by
  intro ℓ w
  have h1 : Continuous fun k : Kinf E a => (Unitary.toUnits k : GL (Fin a) (Cinf E)) :=
    Units.continuous_iff.2 ⟨continuous_subtype_val, continuous_subtype_val.star⟩
  have h2 : Continuous fun k : Kinf E a =>
      ((chiInf χ (Matrix.GeneralLinearGroup.det (Unitary.toUnits k : GL (Fin a) (Cinf E))) : ℂˣ) : ℂ) :=
    Units.continuous_val.comp ((continuous_chiInf χ).comp (Matrix.GeneralLinearGroup.continuous_det.comp h1))
  have e : (fun k : Kinf E a => ℓ (kRep a χ k w)) = fun k =>
      ((chiInf χ (Matrix.GeneralLinearGroup.det (Unitary.toUnits k : GL (Fin a) (Cinf E))) : ℂˣ) : ℂ) * ℓ w := by
    funext k
    rw [← show chiDet a χ (infGL E a (Unitary.toUnits k)) =
      chiInf χ (Matrix.GeneralLinearGroup.det (Unitary.toUnits k)) from congrArg χ.1 (det_infGL _), ← smul_eq_mul,
      ← map_smul]
    rfl
  rw [e]
  exact h2.mul continuous_const


theorem chi_ne_zero (χ : HChar E) : mulChi a χ (oneFn E a) ≠ 0 :=
  (map_ne_zero_iff _ (mulChi a χ).injective).2 oneFn_ne_zero


end GlobalTheory.Published.AutFinGL.Model

end
