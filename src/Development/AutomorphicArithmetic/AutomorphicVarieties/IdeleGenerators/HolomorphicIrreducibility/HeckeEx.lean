module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall
public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.TwoNeZeroNat

@[expose] public section

noncomputable section

open CongruenceSubgroup UpperHalfPlane ModularForm UpperTheory.V.Af
open scoped MatrixGroups ModularForm Manifold

namespace UpperTheory.V.Sd

end UpperTheory.V.Sd

theorem UpperTheory.V.Sd.heckeEx :
    UpperTheory.V.Sd.HeckeEx :=
  _root_.UpperTheory.Reformulated.B.hecke_existence.heckeEx
