import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.UnitaryTwoForm
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.AlgOfCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.PlacesOverFinite.ExistsType
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.PlacesOverFinite.LemTWM
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.IsAlgOfPos
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.UpQuad
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.FrobDual
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.ExistsPrimeIndex
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.AwReal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.AwTw
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.ExistsPrimeIndex
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.PotOrd

open UpperTheory.GalN.V

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Sd
open scoped Matrix

namespace UpperTheory.V.Z.Sym.W










private theorem adjoint_zero_twist {Γ k : Type} [Group Γ] [Field k] (r : Γ →* GL (Fin 2) k) (δ : Γ →* kˣ) : ad0 (tw r δ) = ad0 r := by
  refine MonoidHom.ext fun s => Units.ext ?_
  have hd : (δ s : k) ≠ 0 := (δ s).ne_zero
  have h0 : (r s : Matrix (Fin 2) (Fin 2) k).det ≠ 0 := by
    have := ((Matrix.GeneralLinearGroup.det (r s)).ne_zero)
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using this
  have hD : ((tw r δ s : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).det = (δ s : k) ^ 2 * (r s : Matrix (Fin 2) (Fin 2) k).det := by
    rw [tw_val, Matrix.det_smul]; simp
  simp only [ad0, tw_val, MonoidHom.comp_apply, MonoidHom.inv_apply, Units.coe_map, MonoidHom.coe_coe]
  simp only [Units.val_inv_eq_inv_val, Matrix.GeneralLinearGroup.val_det_apply, hD, ← tw_val]
  simp only [tw_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [symSquareMatrixHom] <;> field_simp


end UpperTheory.V.Z.Sym.W

end
