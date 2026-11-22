module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.AuxiliaryPrimeFunction
public import GroundTheory.AutomorphicForms.AffineBruhat
public import CompanionTheory.EightfoldTheory.VariationTheory.PublishedTheorems.ImportsAlt
public import CompanionTheory.EightfoldTheory.VariationTheory.SelfDualForms.SelfDualWeylChambers.Imports
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FoundBridge
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.HolCap
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.ExistsIdele
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.HolLin
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.ExpInj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.ExpUnique
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.KLocal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.DirChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CharVal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.ArchBd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.LiftEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.LiftSm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.LiftLie
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.LiftCent
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.OrthCases
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.LiftCT
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CuspCrit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.LiftExp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.HkCoef
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.InfGLScalar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Imports
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.SatComp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.SatHol
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.SatOfVec

@[expose] public section

open Formalism.UG GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal Matrix

theorem UpperTheory.isCommensurated_iwahori_gl :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ), IsCommensurated (iwahori k n) := by
  intro k _ _ _ _ n g
  have hO : IsOpen (iwahori k n : Set (GL (Fin n) k)) := isOpen_iwahori k n
  have hC : IsCompact (iwahori k n : Set (GL (Fin n) k)) := isCompact_iwahori k n
  have hset : (((iwahori k n).map (MulAut.conj g).toMonoidHom : Subgroup (GL (Fin n) k)) :
      Set (GL (Fin n) k)) = (fun x => g⁻¹ * x * g) ⁻¹' (iwahori k n : Set (GL (Fin n) k)) := by
    ext x
    simp only [Subgroup.coe_map, Set.mem_image, SetLike.mem_coe, Set.mem_preimage,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [mul_assoc] using hy
    · intro hx
      exact ⟨_, hx, by simp [mul_assoc]⟩
  have hOc : IsOpen (((iwahori k n).map (MulAut.conj g).toMonoidHom : Subgroup (GL (Fin n) k)) :
      Set (GL (Fin n) k)) := by
    rw [hset]
    exact hO.preimage (by fun_prop)
  haveI : CompactSpace (iwahori k n) := isCompact_iff_compactSpace.mp hC
  have hU : IsOpen ((((iwahori k n).map (MulAut.conj g).toMonoidHom).subgroupOf (iwahori k n) :
      Subgroup (iwahori k n)) : Set (iwahori k n)) :=
    hOc.preimage continuous_subtype_val
  haveI := Subgroup.quotient_finite_of_isOpen _ hU
  exact Subgroup.index_ne_zero_of_finite
