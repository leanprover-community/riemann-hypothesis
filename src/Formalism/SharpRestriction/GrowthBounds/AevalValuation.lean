import Formalism.SharpRestriction.GrowthBounds.AevalValuation.MemSupportedOf
import Formalism.SharpRestriction.GrowthBounds.AevalValuation.ValGen
import Formalism.SharpRestriction.GrowthBounds.MonomialSupport.PhMonomialMul
import Formalism.SharpRestriction.GrowthBounds.MonomialSupport.GeZSum
import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution
import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.Proposition5OfThreeParts
import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.GramExponentArithmetic
import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.MembFinal
import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.WithThModelLet
import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.WBound
import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.RestOneOpOf
import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.DoubleMonomialApply
import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.XXgZeroP
import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.GeoTouch
import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.RenameMemSupported
import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.CompDEqHomComp
import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.ValSCongrSupp
import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.PmatDetMem
import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.FortyEightBoundArith
import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.ProdRangeZmod
import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.SupportedOfSupport
import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.SumFiberMultideg
import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.MemTSetIff
import Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.MultidegSingle
import Formalism.SharpRestriction.GrowthBounds.MonomialSupport.Lam1SPderivAndXMulLeAddIndicator

section
noncomputable section

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.TestSideWords

theorem proposition5_holds (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) : Proposition5Gram D CLa Ck Crk Cdeg 26 2 24 60 :=
  proposition5_of_three_parts D CLa Ck Crk Cdeg (restPick D CLa Ck Crk Cdeg) (restMemb D CLa Ck Crk Cdeg) (restNum D CLa Ck Crk Cdeg)

theorem stmtE_of_mem (D : Formalism.BasicNotions.D7) (hM : ∀ CLa Ck Crk Cdeg : ℝ, RestMEM D CLa Ck Crk Cdeg) : tableLineDegreeFive.ClosedFormOfAdmitted D :=
  stmtE_of_MP D hM fun CLa Ck Crk Cdeg => proposition5_holds D CLa Ck Crk Cdeg

end Formalism.MainNotions.Proposition5Numerics
end
end

section
noncomputable section

namespace Formalism.MainNotions.PairMembershipBlocks

open Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords

theorem opSteps_of (h : NoOpStep) : OpSteps :=
  ⟨trDerPl, trDerNo, trMulPl, trMulNo, plDer, plEul, plMul, h, geoTop, geoTouch⟩

theorem restWord_of_steps (h : OpSteps) (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) : RestWord D CLa Ck Crk Cdeg :=
  restWord_of D CLa Ck Crk Cdeg restLeOfG (restOneOp_of h D CLa Ck Crk Cdeg) (restWordBound D CLa Ck Crk Cdeg)

theorem restMEM_of_last (hNO : NoOpStep) (hPl : RestPl)
    (hAr : ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → ∀ CLa : ℝ, RestArithStep C CLa)
    (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg : ℝ) : RestMEM D CLa Ck Crk Cdeg :=
  memCondition_of_theoremII D CLa Ck Crk Cdeg
    (lemma5a_of_monomial D CLa Ck Crk Cdeg
      (rest5aMono_of_cut restT (restN D) restTh hPl restSP hAr D CLa Ck Crk Cdeg))
    (restWord_of_steps (opSteps_of hNO) D CLa Ck Crk Cdeg)

theorem stmtE_of_last (D : Formalism.BasicNotions.D7) (hNO : NoOpStep) (hPl : RestPl)
    (hAr : ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → ∀ CLa : ℝ, RestArithStep C CLa) : tableLineDegreeFive.ClosedFormOfAdmitted D :=
  Formalism.MainNotions.Proposition5Numerics.stmtE_of_mem D (fun CLa Ck Crk Cdeg => restMEM_of_last hNO hPl hAr D CLa Ck Crk Cdeg)

theorem stmtE_of_pl (D : Formalism.BasicNotions.D7) (hPl : RestPl) : tableLineDegreeFive.ClosedFormOfAdmitted D :=
  stmtE_of_last D Formalism.MainNotions.LetterSubstitution.noOpStep hPl ⟨1, one_pos, fun C hC CLa => arithCondition_of_one_le C CLa hC⟩

theorem level_link_of_degree_letters (hLL : LinkL) (hDg : LkDeg) (hVr : LkVars) : RestLink :=
  restLink_of Formalism.MainNotions.LetterSubstitution.valNN Formalism.MainNotions.LetterSubstitution.homDec hLL hDg hVr restTr (fun Fr jz μ => lkW Fr jz μ)

private theorem restPl_of_restChain_of_restLink (hC : RestChain) (hL : RestLink) : RestPl := by
  intro p _ n' r K m _ _ _ O _ _ _ _ hk Fr L₁ N₁ hV hE J _ Dt hT hJ A hA l hl ga hg t ht dPl
  exact ⟨hC p n' r K m O hk Fr L₁ N₁ hV hE J Dt hT hJ A hA l hl ga hg t ht dPl,
    hL p n' r K m O hk Fr L₁ N₁ hV hE J Dt hT hJ A hA l hl ga hg t ht dPl⟩

theorem restLink : RestLink := level_link_of_degree_letters linkL lkDeg lkVars

theorem stmtE_of_chain (D : Formalism.BasicNotions.D7) (hC : RestChain) : tableLineDegreeFive.ClosedFormOfAdmitted D :=
  stmtE_of_pl D (restPl_of_restChain_of_restLink hC restLink)

end Formalism.MainNotions.PairMembershipBlocks
end
end

section
namespace Formalism.MainNotions.TraceSpectra

theorem restChain : Formalism.MainNotions.PairMembershipBlocks.RestChain :=
  restChain_of valAeval valFilt Formalism.MainNotions.LetterSubstitution.valNN Formalism.MainNotions.LetterSubstitution.phMon Formalism.MainNotions.LetterSubstitution.compPh Formalism.MainNotions.LetterSubstitution.fdigPh
    Formalism.MainNotions.LetterSubstitution.fdigSum

theorem stmtE (D : Formalism.BasicNotions.D7) : tableLineDegreeFive.ClosedFormOfAdmitted D := Formalism.MainNotions.PairMembershipBlocks.stmtE_of_chain D restChain

end Formalism.MainNotions.TraceSpectra
end
