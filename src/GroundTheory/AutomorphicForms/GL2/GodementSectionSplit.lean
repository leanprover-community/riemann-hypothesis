module

public import Mathlib
public import GroundTheory.AutomorphicForms.GL2.GodementSection
public import GroundTheory.GlobalFields.TateThesis.HeckeCharRayClass

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology NumberField.mixedEmbedding
open scoped NumberField.AdeleRing SchwartzMap Classical

namespace GroundTheory.Automorphic.GodementSection

open GroundTheory.Global GroundTheory.Automorphic.Adele2 IdeleGroup

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

theorem toInfinite_symm (p : (InfiniteAdeleRing K)ˣ × (FiniteAdeleRing (𝓞 K) K)ˣ) :
    toInfinite K ((IdeleGroup.prodEquiv K).symm p) = p.1 := by
  change (IdeleGroup.prodEquiv K ((IdeleGroup.prodEquiv K).symm p)).1 = p.1
  rw [ContinuousMulEquiv.apply_symm_apply]

theorem toFinite_symm (p : (InfiniteAdeleRing K)ˣ × (FiniteAdeleRing (𝓞 K) K)ˣ) :
    toFinite K ((IdeleGroup.prodEquiv K).symm p) = p.2 := by
  change (IdeleGroup.prodEquiv K ((IdeleGroup.prodEquiv K).symm p)).2 = p.2
  rw [ContinuousMulEquiv.apply_symm_apply]

end

end GroundTheory.Automorphic.GodementSection
