module

public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.CuspSpanNormBounds.LeSCSCl
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.SharpRestriction.CuspSpanNormBounds.StandingNumericalData
public import Formalism.SharpRestriction.CuspSpanNormBounds.FlagEEqHyperbolic
public import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
public import Formalism.SharpRestriction.CuspSpanNormBounds.CntPartners
public import Formalism.HermitianLattices.StatementMass
public import Formalism.ThetaLiftIndependence.Statement
public import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds

@[expose] public section

noncomputable section

open NumberField MeasureTheory
open scoped ENNReal

namespace Formalism.MainNotions.LatticeIndexAndWeightTheory

export Formalism.MainNotions.S.UnitaryVolumeMass (KTwoParameterConditions Kpp)

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Hyps

variable (D : D7) (large₂ : SizeData₂ D)

end Hyps

section TermObj

variable {D : D7} (X : TermTie D) {u u' : D.what₂.Word} (t : D.s.Term u u')

end TermObj

section Datum

variable {D : D7} (X : TermTie D) {u u' : D.what₂.Word}

end Datum

section Terms

variable (D : D7) (large₂ : SizeData₂ D) (X : TermTie D)

end Terms

section Size

variable (D : D7) (large₂ : SizeData₂ D)

end Size

section Mass

variable (D : D7) (large₂ : SizeData₂ D)

end Mass

section Targets

variable (D : D7) (large₂ : SizeData₂ D) (X : TermTie D)

end Targets

section Packet

variable (D : D7) (large₂ : SizeData₂ D) (X : TermTie D) (G : GlobalTheoryTheory.GenusMassVolumes.GaugeFam D.host.F D.host.E D.sp.cm.sig)

end Packet

section Family

variable {eps : ℝ} (Fm : FamP eps) (At : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))

end Family

end Formalism.MainNotions.LatticeIndexAndWeightTheory

end
