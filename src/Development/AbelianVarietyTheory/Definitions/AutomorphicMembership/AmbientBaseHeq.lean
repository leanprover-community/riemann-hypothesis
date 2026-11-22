module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PointPropertyEqSizeFree
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FamilyClassSevenDutiesAndStableLattices
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleIndexBoundAllPowers
public import Formalism.LocalToGlobal.BesselHermitianTheta.MinfDensity

@[expose] public section

noncomputable section

namespace GlobalTheory.Mem.Top

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField IsDedekindDomain

structure ColLay (D : D7) (lev : LevelData D) (eX : ErrX D) : Prop where
  piG_lev : PiGLevel D lev eX
  piT_lev : PiTLevel D lev eX
  seen : SeenDef D eX
  tauOf : TauOfDef D eX
  one : ∀ u μ, (D.chTw u μ).DGam = (D.mem D.u₀).C.DGam
  mink : DGamChoice_at D
  atT : ∀ u (w : D.what₂.places.Pl), D.what₂.places.resChar w = (D.mem u).A.T → ∃ n : ℕ, n ≠ 0 ∧
    (∀ x ∈ DV.MramL D u, D.nuIn u (n • x) ∈ LT.Nlam D u w) ∧
    ∀ x, D.nuIn u x ∈ LT.Nlam D u w → InLoc (D.plEq w) (DV.MramL D u) (n • x)

def GatNum (s : Scale) (D : D7) : Prop :=
  ∀ u w hg, (D.gat u w hg).P.r = (if (D.what₂.places.resChar w : ℝ) < s.p0 D.R.k then G.rG s else 1) ∧
    (D.gat u w hg).e = ⌈(1 : ℝ) * (D.R.f : ℝ) * (D.R.k : ℝ) ^ 2 * Real.logb (D.what₂.places.resChar w) s.a⌉₊

structure GyLay (K : Ctx) (D : D7) (Gt : GatTies D) (cmp : LatCmp D) (Gy : G.LatInst D) : Prop where
  vram : cmp.VramDef Gy
  fills : FillsAll Gt Gy
  led : ∀ L : SizeData₂ D, L.sc = K.s → WtEq L K.a K.b → Val K.C K.cD K.ch L → ∀ X : G.Inst D L, CanonInst X → G.EpDef X K.C.cX.Ce →
    G.KapIDef X K.C.GK → (∀ w, G.ParametersFill X K.C.GK w) → G.LatTied Gt X Gy

def ExportAt (D : D7) (nch : NChoice D) (xd : ThData D) : Prop :=
  ∃ (N0 : D.ntw.Tw → ℕ) (S : ∀ (i : D.ntw.Tw) (j : ℕ) (b : Bool), Finset (D.nexp.Dat i j b)),
    (∀ i, D.ntw.NonzeroIndexPlace i → GlobalTheory.TwAll.goodTwistExistsAllCoprimePowers D.nexp (BlochKatoReduction.pin (BlochKatoReduction.bk0 D)) (twEOf xd) N0 i) ∧
    ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 →
      BlochKatoReduction.Gen.SetHyp (BlochKatoReduction.bk0 D) (nch.twI w) ∧ TwIn.Ok (⟨twEOf xd, N0, S⟩ : TwIn D) (nch.twI w)

section Lemmas

variable {D : D7}

end Lemmas

end GlobalTheory.Mem.Top

end
