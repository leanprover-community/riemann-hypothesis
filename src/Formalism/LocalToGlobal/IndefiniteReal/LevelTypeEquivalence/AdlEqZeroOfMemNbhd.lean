module

public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Formalism.LocalToGlobal.GlobalTheory.GL1.CompactFixesLattice.ExistsDenOfIsCompactAdele
public import Formalism.LocalToGlobal.AdelicCompactOpens.IntAdelesCompactOpen
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdicIntegersCompact.IsCompactAdicCompletionIntegers
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactAdeleRingModNumberField
import Mathlib.Tactic.Linter.Style

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain

namespace Formalism.IndefR.Eqv.G5

variable {F : Type} [Field F] [NumberField F]

open scoped AdeleRing

variable (F) in
def adlNbhd (F : Type) [Field F] [NumberField F] : Set (AdeleRing (𝓞 F) F) :=
  {x | (∀ w, ‖x.1 w‖ < 1) ∧ ∀ v, x.2 v ∈ v.adicCompletionIntegers F}

theorem adl_inf_cocompact : ∃ C : Set (InfiniteAdeleRing F), IsCompact C ∧
    ∀ y, ∃ r : 𝓞 F, y - algebraMap F _ (r : F) ∈ C := by
  apply GlobalTheory.AdeleCocompact.exists_compact_infinite

theorem adl_cocompact : ∃ K : Set (AdeleRing (𝓞 F) F), IsCompact K ∧
    ∀ x, ∃ a : F, x - algebraMap F _ a ∈ K := by
  obtain ⟨C, hC, hCy⟩ := adl_inf_cocompact (F := F)
  refine ⟨C ×ˢ {x : FiniteAdeleRing (𝓞 F) F | ∀ v, x v ∈ v.adicCompletionIntegers F},
    hC.prod (_root_.PI.IntAdCpctOpenWork.main F).2, fun x => ?_⟩
  obtain ⟨u, hu⟩ := Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.exists_sub_mem_intAd x.2
  obtain ⟨r, hr⟩ := hCy (x.1 - algebraMap F _ u)
  refine ⟨u + r, ?_, ?_⟩
  · show x.1 - algebraMap F (InfiniteAdeleRing F) (u + r) ∈ C
    rw [map_add (f := _), ← sub_sub]
    exact hr
  · have : x.2 - algebraMap F (FiniteAdeleRing (𝓞 F) F) (u + r) =
        (x.2 - algebraMap F _ u) - algebraMap F _ (r : F) := by rw [map_add (f := _), sub_sub]
    show ∀ v, (x.2 - algebraMap F (FiniteAdeleRing (𝓞 F) F) (u + r)) v ∈ _
    rw [this]
    exact sub_mem hu (Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.algebraMap_mem_intAd r)

end Formalism.IndefR.Eqv.G5
