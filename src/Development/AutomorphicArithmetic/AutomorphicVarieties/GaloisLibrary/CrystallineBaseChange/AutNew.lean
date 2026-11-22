module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.HolVec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.LevelVec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CharOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Deadel
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.NormSpan
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.ClTwist
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.Unitarize
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.SatLocFree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.MinNew
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CharEq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.AbsExpo
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CharpolySmul
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.IsHermOfInner
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CuspidalFiniteness.ExistsZalgOfCenterU

@[expose] public section

open NumberField GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af


open GroundTheory.Automorphic in
theorem UpperTheory.V.Br.hermEx : Gk.HermEx :=
  Gk.hermEx_of (fun _ _ _ _ _ => CuspFin.mem_cuspForms_of) fun F _ _ _ a => by
    refine ⟨(Fb.lieEq F a).toLinearMap, Subtype.ext ?_, fun X φ _ => congrArg Subtype.val (CuspFin.uAction_lieEq X φ)⟩
    rw [UnitaryAdmissible.coe_centralZ, Algebra.algebraMap_eq_smul_one, ← Fb.lieEq_oneL]
    rfl
