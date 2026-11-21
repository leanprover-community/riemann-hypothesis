import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ActOOneResGCompl

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open Formalism.IndefR.Fin.LevelGroupLemmas (resG detAt)

namespace GlobalTheory.IdemSumF

theorem exists_idem_below : ∀ {D : D7} {P : Finset (Pl D.host.E)} {e : AE D}, IsIdemSum e P →
    ∃ ε : AF D.host.F, IsIdempotentElem ε ∧ algebraMap (AF D.host.F) (AE D) ε = e + cA D e :=
  fun he => Formalism.IndefR.Fin.LevelGroupLemmas.idemSum_eps he

end GlobalTheory.IdemSumF
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open Formalism.IndefR.Fin.LevelGroupLemmas (resG detAt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_baseIdempotent_of_splitIdempotentSum : ∀ {D : D7} {P : Finset (Pl D.host.E)} {e : AE D}, IsIdemSum e P →
    ∃ ε : AF D.host.F, IsIdempotentElem ε ∧ algebraMap (AF D.host.F) (AE D) ε = e + cA D e := by
  atlas_forward_decl GlobalTheory.IdemSumF.exists_idem_below
