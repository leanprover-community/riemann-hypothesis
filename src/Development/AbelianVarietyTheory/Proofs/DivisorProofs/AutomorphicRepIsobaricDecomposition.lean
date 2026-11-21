import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeDefinite
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangeSpehOfDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpehShapeIffOfDiscreteSpectrum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockValAe
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConjugateSplitPlaceOffStableSet
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFamilyIffRationalHecke

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Mult Formalism.UG GlobalTheory.SphPar GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.HostBC

theorem spehSat_eq (q d : ℕ) (B : Multiset ℂˣ) : GlobalTheory.SphGal.spehSat q d B =
    ∑ k : Fin d, B.map (fun z : ℂˣ => (z : ℂ) * (q : ℂ) ^ (((d : ℂ) - 1) / 2 - (k : ℕ))) := by
  unfold GlobalTheory.SphGal.spehSat
  rw [← Equiv.sum_comp Fin.revPerm]
  refine Finset.sum_congr rfl fun k _ => Multiset.map_congr rfl fun z _ => ?_
  have hk : ((k.rev : ℕ) : ℂ) = d - (k + 1) := by
    rw [Fin.val_rev, Nat.cast_sub (Nat.succ_le_of_lt k.2)]
    push_cast
    rfl
  simp only [Fin.revPerm_apply, hk]
  congr 2
  ring


end GlobalTheory.HostBC

namespace GlobalTheory.HostBC

open GlobalTheory.DiscSpec GlobalTheory.DefiniteBC

theorem sum_map_val {c : ℕ} (q : ℕ) (d : Fin c → ℕ) (B S : Fin c → Multiset ℂˣ)
    (h : ∀ i, ∑ k : Fin (d i), (B i).map (fun z : ℂˣ => (z : ℂ) * (q : ℂ) ^ (((d i : ℂ) - 1) / 2 - (k : ℕ))) =
      (S i).map (fun z : ℂˣ => (z : ℂ))) :
    (∑ i, S i).map (fun z : ℂˣ => (z : ℂ)) = ∑ i, GlobalTheory.SphGal.spehSat q (d i) (B i) := by
  refine (map_sum (Multiset.mapAddMonoidHom fun z : ℂˣ => (z : ℂ)) _ _).trans ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [spehSat_eq, h]
  rfl

end GlobalTheory.HostBC

namespace GlobalTheory.HostBC

open GlobalTheory.DiscSpec GlobalTheory.DefiniteBC


end GlobalTheory.HostBC

end
