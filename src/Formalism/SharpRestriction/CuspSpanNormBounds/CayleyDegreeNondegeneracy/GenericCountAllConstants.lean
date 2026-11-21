import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.PrimitiveMeanOverWords
import Formalism.SharpRestriction.CuspSpanNormBounds.AutLzFiniteOfLoop

noncomputable section

open scoped Classical

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.BridgeLemma
open scoped ENNReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar


section Num

variable (D : D7) (large₂ : SizeData₂ D)










end Num

section C4

variable (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word)

def PartnerThetaInclusion (C' Cl Cg cb Cu cT CT C0 A : ℝ) : Prop :=
  Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A →
  ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
  ∀ Λ : LatV D, IsRowLat D F0 Λ →
  ∀ F' : FlagU D u', IsTermF D Λ (lf D F0) F' → IsGeneric Λ (gS D) (lf D F0) F' → ∀ Z : GramM D,
  ∀ F'' ∈ Partners D Λ (lf D F0) F' Z,
    latticeTraceOnW D (lf D F0) (Thp Λ (lf D F0) F') ≤ latticeTraceOnW D (lf D F0) (Thp Λ (lf D F0) F'')

def GenericThetaSublattice (C' Cl Cg cb Cu cT CT C0 A C : ℝ) : Prop :=
  Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A →
  ∀ F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E), F0.e = D.sp.hypE → F0.z = D.zmOf u →
  ∀ Λ : LatV D, IsRowLat D F0 Λ →
  ∀ F' : FlagU D u', IsTermF D Λ (lf D F0) F' → IsGeneric Λ (gS D) (lf D F0) F' → RelZ D (ZhatL (lf D F0) F') →
    latticeTraceOnW D (lf D F0) (Thp Λ (lf D F0) F') ≤ L0X D Λ (lf D F0) ∧
    latticeRank D (latticeTraceOnW D (lf D F0) (Thp Λ (lf D F0) F')) = D.R.k - 1 ∧
    latticeDetW D (latticeTraceOnW D (lf D F0) (Thp Λ (lf D F0) F')) ≤ HHZ D large₂.sc.b C (ZhatL (lf D F0) F')

end C4

section C4F

variable {eps : ℝ} (Fm : FamP eps)

def PositionCountFamilyGeneric (Cg cb Cu cT CT C0 A : ℝ) : Prop :=
  ∃ C₀ : ℝ, ∀ C ≥ C₀, OwnEv Fm fun C' Cl x i => ∀ u u',
    TermPositionCount (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A C

def PartnerThetaFamily (Cg cb Cu cT CT C0 A : ℝ) : Prop :=
  OwnEv Fm fun C' Cl x i => ∀ u u', PartnerThetaInclusion (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A

def GenericThetaFamily (Cg cb Cu cT CT C0 A : ℝ) : Prop :=
  ∃ C₀ : ℝ, ∀ C ≥ C₀, OwnEv Fm fun C' Cl x i => ∀ u u',
    GenericThetaSublattice (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A C

end C4F


section Mean

variable (D : D7)



end Mean

end Formalism.MainNotions.BridgeLemma₂

end
