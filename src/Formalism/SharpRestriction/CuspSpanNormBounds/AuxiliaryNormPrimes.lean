module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.DataParams₂
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.CuspSpanNormBounds.LeSCSCl
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.SharpRestriction.CuspSpanNormBounds.StandingNumericalData
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
public import Formalism.SharpRestriction.CuspSpanNormBounds.FlagEEqHyperbolic
public import Formalism.SharpRestriction.CuspSpanNormBounds.CntPartners
public import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
public import Formalism.HermitianLattices.StatementMass
public import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.AuxiliaryNormPrimes

export Formalism.MainNotions.S.UnitaryVolumeMass (embU succMin dualZ)

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Cnt NumberField Matrix Module
open scoped ENNReal NNReal InnerProductSpace

section B3

open Formalism.MainNotions.S.Lat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

end B3

section Mass

open Formalism.MainNotions.S.Lat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end Mass

section BR

end BR

section Rows

open Formalism.MainNotions.S.Lat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

end Rows

def TemperatureProductAsymptotic (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 δ : ℝ) : Prop :=
  UnitaryVolumeMass.stTprod D large₂ C' Cl Cg cb Cu cT CT C0 δ

section Loc

open MeasureTheory Finset Formalism.QuantumDeterminants

variable (D : D7) (large₂ : SizeData₂ D)

def PlancherelBoundOneParameter (C' Cl Cg cb Cu cT CT C0 Cn C1 C : ℝ) : Prop :=
  UnitaryVolumeMass.stPT D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 C

end Loc

section Comparison₂

open Formalism.MainNotions.S.Lat MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end Comparison₂

section Stmt

variable (D : D7) (large₂ : SizeData₂ D) (X : TermTie D) (u u' : D.what₂.Word) (C1 : ℝ) (Y : LoopTie D large₂ X u u' C1)
  (G : letI := D.host.cmStar; GlobalTheoryTheory.GenusMassVolumes.GaugeFam D.host.F D.host.E D.sp.cm.sig)

end Stmt

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

def FamilyTemperatureProductAsymptotic (Cg cb Cu cT CT C0 : ℝ) : Prop :=
  ∀ δ > 0, OwnEv Fm fun C' Cl x i => TemperatureProductAsymptotic (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 δ

variable (C1 : ℝ) (X : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))
  (Y : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word),
    LoopTie (Fm.D x i) (Fm.L x i) (X x hx i) u u' C1)

end Family

end Formalism.MainNotions.AuxiliaryNormPrimes
