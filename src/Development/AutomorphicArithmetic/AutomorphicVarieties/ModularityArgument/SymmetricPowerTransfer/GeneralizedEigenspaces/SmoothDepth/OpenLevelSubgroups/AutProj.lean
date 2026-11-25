module

import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.DecompA
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MkMemAdmissibleAtIffCocycle
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsCompactFundamentalSetUnitary
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsEquivariantProjectionsOfSumIrreducible
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsNondegenerateRightInvariantFormOfCompactQu
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.MemISupAutomorphicRepsOfInvariantForm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.UnitaryAdelicGroupTopology
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.IsLevel
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.ContCoef
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.Wcount
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

open UpperTheory.V.Z.Sym.Al

open GlobalTheory.DefU in
theorem UpperTheory.V.Z.Sym.Al.autProj :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (M : Submodule ℂ (GlobalTheory.DefU.autU L n)), FiniteDimensional ℂ M →
        ∃ (κ : Type) (_ : Fintype κ) (σ : κ → Submodule ℂ (UA L n → ℂ)) (P : κ → GlobalTheory.DefU.autU L n →ₗ[ℂ] GlobalTheory.DefU.autU L n),
          (∀ i, IsAutRepU (σ i)) ∧ (∀ i φ, (P i φ).1 ∈ σ i) ∧
          (∀ i x φ, P i (GlobalTheory.DefU.autRep L n x φ) = GlobalTheory.DefU.autRep L n x (P i φ)) ∧ ∀ φ ∈ M, ∑ i, P i φ = φ := @_root_.UpperTheory.V.Z.J.D.Dc.autProj
