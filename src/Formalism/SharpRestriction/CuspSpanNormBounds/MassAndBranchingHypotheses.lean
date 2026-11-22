module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.CuspSpanNormBounds.LeSCSCl
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.SharpRestriction.CuspSpanNormBounds.StandingNumericalData
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
public import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
public import Formalism.SharpRestriction.CuspSpanNormBounds.FlagEEqHyperbolic
public import Formalism.SharpRestriction.CuspSpanNormBounds.CntPartners
public import Formalism.HermitianLattices.StatementMass
public import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.VanishingOnXAndXPlusMass

export Formalism.MainNotions.S.UnitaryVolumeMass (embU succMin dualZ)

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt
open scoped ENNReal NNReal InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Conclusion₂

variable (D : D7)

def Conclusion1 (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A C c : ℝ) : Prop :=
  UnitaryVolumeMass.stX D large₂ u u' C' Cl Cg cb Cu cT CT C0 A C c

def PointsLemma (u : D.what₂.Word) : Prop :=
  UnitaryVolumeMass.stLem3L0 D u

end Conclusion₂

section admitted

variable (D : D7)

def adm1 : Prop :=
  UnitaryVolumeMass.stMassRatio D

end admitted

section Loc

open MeasureTheory Finset Formalism.QuantumDeterminants

variable (D : D7) (large₂ : SizeData₂ D)

end Loc

section Stmt

variable (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (G : GlobalTheoryTheory.GenusMassVolumes.GaugeFam D.host.F D.host.E D.sp.cm.sig)

end Stmt

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

def Conclusion3Family : Prop := ∀ x, Fm.x1 < x → ∀ (i : Fm.Ix x) u, PointsLemma (Fm.D x i) u

end Family

end Formalism.MainNotions.VanishingOnXAndXPlusMass

end
