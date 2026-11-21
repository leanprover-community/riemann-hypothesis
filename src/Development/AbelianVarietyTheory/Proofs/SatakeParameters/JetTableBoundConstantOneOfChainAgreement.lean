import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JetSplitAmb
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Formalism.LocalToGlobal.GroupLattices.AdmissibleAtGeneratorPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PeriodValuationBoundTypePrimePlaceOfChainAgreeme

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Fc GlobalTheory.Mem.Top GlobalTheory.AtG

namespace GlobalTheory.AtG

theorem jetTableBound_constantOne_of_chainAgreement : JetSplitAmb → ∀ (D : D7) (L : SizeData₂ D) (EX : ErrX D) (Dx : DivX D),
    (∀ μ, (μ = D.what₂.mu0 ∨ ∃ w, μ = D.what₂.muAt w) → TiesAt D EX Dx μ) → (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound.SizeAt D i) →
    Formalism.L2.G.Adm2InU.UsedTuplesBoundByConstant D L EX 1 := by
  intro hJ D L EX Dx hT hS i w hw u hu μ hμ
  exact GlobalTheory.T.periodValuationBound_typePrimePlace_of_chainAgreement hJ D L EX Dx μ (hT μ hμ) i (hS i) w hw u hu

end GlobalTheory.AtG
end

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Fc GlobalTheory.Mem.Top GlobalTheory.AtG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.propositionCOneUsedTuples_one_of_tiesAt_sizeAt : JetSplitAmb → ∀ (D : D7) (L : SizeData₂ D) (EX : ErrX D) (Dx : DivX D), (∀ μ, (μ = D.what₂.mu0 ∨ ∃ w, μ = D.what₂.muAt w) → TiesAt D EX Dx μ) → (∀ i, GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound.SizeAt D i) → Formalism.L2.G.Adm2InU.UsedTuplesBoundByConstant D L EX 1 := by
  atlas_forward_decl GlobalTheory.AtG.jetTableBound_constantOne_of_chainAgreement
