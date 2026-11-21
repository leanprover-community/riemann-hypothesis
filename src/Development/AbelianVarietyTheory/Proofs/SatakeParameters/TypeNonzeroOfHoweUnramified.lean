import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HypothesesX
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RallisConvOfSteps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SwSection
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralNeTopOfBounds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TermInv
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KerAbsOfCuspRapidDecay
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspKillHolds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftRowsInjectiveAndTypePropertiesOfNonvanishing
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HoweUnramifiedLiftStatement

section
open Formalism.BasicNotions

namespace GlobalTheory.RawLift.Assembled

theorem rallisConv_of_siegelWeil : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.WeilSiegelFormulaUnitary →
    ∀ D : D7, GlobalTheory.RawLift.RallisConv D :=
  fun hP hW D => GlobalTheory.RawLift.rallisConv_of_steps D (GlobalTheory.SWPairProof.swPair hW D) (GlobalTheory.EisAbsPf.eisAbs hP D)
    (GlobalTheory.RawLift.kerAbs_of_cuspRapidDecay hP D) (GlobalTheory.RawLift.Move.termMove D) (GlobalTheory.TermInvProof.termInv D)
    (GlobalTheory.CuspKillProof.cuspKill_holds D)

end GlobalTheory.RawLift.Assembled
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Host

namespace GlobalTheory.DownLift.AtReal

theorem main : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Hk3.HoweUnram → GlobalTheory.NRows.HypothesesX → ∀ (D : D7) (cf : CharFrame D)
    (nch : NChoice D) (tp : TupTied D cf nch) (X : GlobalTheory.NJoin.RealAt D cf nch tp) j t, GlobalTheory.DownLift.TypeNZ X.R j t := by
  intro hP hH hX D cf nch tp X j t
  have hR : GlobalTheory.RawLift.RallisConv D := GlobalTheory.RawLift.Assembled.rallisConv_of_siegelWeil hP hX.sw D
  have hN : ∀ i t, GlobalTheory.DownLift.NonVan X.R i t := fun i t =>
    GlobalTheory.T.howe_unramified_lift hP hX.dbl hX.ft hX.udbl hX.hl hH D X.G X.Pl0 X.T X.A X.Ks X.R X.F X.given X.full i t
  exact ((GlobalTheory.T.liftInj_and_properties_of_rallis_of_nonVan hP hH D X.G X.Pl0 X.T X.A X.Ks X.R X.F X.given X.full hR hN).2 j t).1

end GlobalTheory.DownLift.AtReal
end
