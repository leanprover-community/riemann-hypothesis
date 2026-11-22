module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
public import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.UnitBracket
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Definitions.Foundations.WittIndexEqZeroIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory GlobalTheory.Doubling
open scoped TensorProduct ENNReal NNReal ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def schwartzA (θ : InfFam D) (m n : ℕ) : Submodule ℂ (Mx D m n → ℂ) :=
  Submodule.span ℂ {φ | ∃ (f : SchwartzMap (D.what₂.Tau → Fin m → Fin n → ℂ) ℂ)
    (g : (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ),
      g ∈ WeilM.SB (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) ∧
      φ = fun x => f (fun τ i j => compAt θ τ x i j) * g (fun i j => finPart D (x i j))}

variable (A B : HSp D)

variable {A B}

variable (A B)

end GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz

end
