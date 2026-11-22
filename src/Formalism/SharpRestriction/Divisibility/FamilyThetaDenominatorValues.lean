module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsIdealDenominator
public import Formalism.SharpRestriction.LevelLetterCocycles.TwGood
public import Formalism.SharpRestriction.LevelLetterCocycles.LocsCoverTw
public import Formalism.LocalRingCardinality.DataForced
public import Formalism.SharpRestriction.Divisibility.CartierLocalBounds
public import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
public import Formalism.LocalRingCardinality.DataParamsT

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions
open scoped TensorProduct

namespace Formalism.MainNotions.PDVN

variable (D : Formalism.BasicNotions.D7)

attribute [instance] PtTie.acgHA PtTie.modHA PtTie.acgLA PtTie.modLA

section Run

variable {D} {CH : NChoice D} (X : LiftErrorLocal.Loc D CH)

end Run

section AdmON

variable {D} (L : SizeData₂ D) {CH : NChoice D} {Xd : DivX D} (O : ONObj D CH Xd)

end AdmON

section FamON

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (OF : ONObjF Fm)

end FamON

end Formalism.MainNotions.PDVN

end
