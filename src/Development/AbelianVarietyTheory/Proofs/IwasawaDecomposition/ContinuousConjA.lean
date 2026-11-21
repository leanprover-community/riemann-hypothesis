import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.SymplecticTensorMeasures
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IntegralTransport

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.SymplecticTensorMeasures (cE cE_cE cA_inc cA_cA ConjIsom conj_map_mem_unitaryGroup)
open GlobalTheory.LocWCompare
open scoped TensorProduct

namespace GlobalTheory.ConjAutProps

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D}

theorem continuous_conjA (D : D7) : Continuous (cA D) := by
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  have := IsModuleTopology.continuous_of_linearMap
    (Algebra.TensorProduct.map (AlgHom.id (AF D.host.F) (AF D.host.F)) D.sp.cm.sig).toLinearMap
  exact this

theorem continuous_aut (s : ConjIsom V) : Continuous s.aut := by
  have : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  have hm : Continuous (matHom V) := continuous_subtype_val
  have hmap : Continuous fun x : Matrix (Fin V.rank) (Fin V.rank) (AE D) => x.map (cA D) :=
    continuous_id.matrix_map (continuous_conjA D)
  have hc : Continuous (cG D V.rank) :=
    Units.continuous_iff.2 ⟨hmap.comp Units.continuous_val, hmap.comp Units.continuous_coe_inv⟩
  have h : Continuous fun g : GA D V => s.PA * cG D _ (matHom V g) * s.PA⁻¹ :=
    (continuous_const.mul (hc.comp hm)).mul continuous_const
  exact h.subtype_mk fun g => (s.aut g).2







end GlobalTheory.ConjAutProps

end
