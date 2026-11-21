import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.EFinSmulEqOfFinPart
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.SobSym
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.IpTheta
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.ContinuousSplitInv

section
namespace Formalism.IndefR.Eqv

open scoped ContDiff
open Filter Topology

section MD

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

noncomputable def md (φ : V → ℂ) : (n : ℕ) → (Fin n → V) → ℝ → V → ℂ
  | 0, _, _, a => φ a
  | n + 1, v, h, a => (md φ n (Fin.tail v) h (a + h • v 0) - md φ n (Fin.tail v) h a) / h


end MD

section MD2

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]



theorem contDiff_fderiv_apply {φ : V → ℂ} (hφ : ContDiff ℝ ∞ φ) (w : V) : ContDiff ℝ ∞ (fun y => fderiv ℝ φ y w) :=
  (ContinuousLinearMap.apply ℝ ℂ w).contDiff.comp (hφ.fderiv_right (m := ∞) (by simp))


end MD2

section MD3

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]




end MD3

end Formalism.IndefR.Eqv
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField Filter Topology
open scoped TensorProduct ContDiff

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S T : HSp D} {k : ℕ}

def actOAdd (g : GA D S) (h : GA D T) : WO S T →+ WO S T := AddMonoidHom.mk' (actO S T g h) (actO_add g h)

theorem continuous_actO (g : GA D S) (h : GA D T) : Continuous (actO S T g h) := by
  unfold actO
  exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const



end Formalism.IndefR.Eqv

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField Filter Topology
open scoped TensorProduct ContDiff

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S T : HSp D} {k : ℕ}





end Formalism.IndefR.Eqv

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField Filter Topology
open scoped TensorProduct ContDiff ENNReal

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S T : HSp D} {k : ℕ}


end Formalism.IndefR.Eqv

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField Filter Topology
open scoped TensorProduct ContDiff ENNReal

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S T : HSp D} {k : ℕ}


end Formalism.IndefR.Eqv

end
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField Filter Topology
open scoped TensorProduct ContDiff ENNReal

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S T : HSp D} {k : ℕ}


theorem continuous_psiT (τ : D.what₂.Tau) : Continuous (psiT D τ) := by
  have heq : (psiT D τ : AE D → ℂ) = fun x => gW D (plW D τ) (fstA D.host.F ((basAF D).repr x 0)) +
      gW D (plW D τ) (fstA D.host.F ((basAF D).repr x 1)) * betaT D τ := by
    funext x
    simp only [psiT, RingHom.coe_comp, Function.comp_apply]
    rw [thetaC_decomp, repr_infPart, repr_infPart]
  rw [heq]
  have hc : ∀ k : Fin 2, Continuous fun x : AE D => (basAF D).repr x k := fun k => by
    have := (continuous_apply k).comp (G5.tensCoordH (basE D) (AF D.host.F)).continuous
    convert this using 1
    funext x
    simp only [Function.comp_apply, G5.tensCoordH_apply]
    rfl
  have hf : Continuous (fstA D.host.F) := continuous_fst
  exact ((continuous_gW (D := D) _).comp (hf.comp (hc 0))).add
    (((continuous_gW (D := D) _).comp (hf.comp (hc 1))).mul continuous_const)

end Formalism.IndefR.Eqv

end
end
