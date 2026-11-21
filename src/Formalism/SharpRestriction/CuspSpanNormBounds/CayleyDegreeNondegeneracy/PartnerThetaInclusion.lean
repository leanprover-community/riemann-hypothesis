import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.GenericAdmissibleFamilyOfSteps
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.FibreCountOfFirstSteps

noncomputable section

open scoped Classical

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.LatticeGluingRadicals
open scoped ENNReal

section GenG

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {r : ℕ}
  {Λ : Submodule (𝓞 E) S.V} {g : ℕ} {T T' : E} {F : LFlag S r T} {F' : LFlag S r T'}


end GenG

section GenG2

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {r : ℕ}
  {Λ : Submodule (𝓞 E) S.V} {g : ℕ} {T T' : E} {F : LFlag S r T} {F' : LFlag S r T'}



end GenG2

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word)

def GenericIndexOne (C' Cl Cg cb Cu cT CT C0 A : ℝ) : Prop :=
  Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A →
  ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
  ∀ Λ : LatV D, IsRowLat D F0 Λ →
  ∀ F' : FlagU D u', IsTermF D Λ (lf D F0) F' → IsGeneric Λ (gS D) (lf D F0) F' →
    La Λ (gS D) (lf D F0) F' ≤ Thp Λ (lf D F0) F'


end Gen

end Formalism.MainNotions.BridgeLemma₂

end
