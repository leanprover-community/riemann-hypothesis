module

public import Formalism.LocalToGlobal.JointCharacters.LocEMulLocE
public import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField ReciprocityTheory.Neutral.Bridge.HCFR
open scoped TensorProduct

namespace Formalism.L2.JoinChr

open Formalism.L2.Theta Formalism.L2.Host

structure SameChr {D : D7} {X : ThetaX D} {C : CharFrame D} {nch : NChoice D} {Tp : TupTied D C nch}
    (T : ThetaTied D X) (H : ThetaChrTied D C nch Tp X) : Prop where

end Formalism.L2.JoinChr

end
