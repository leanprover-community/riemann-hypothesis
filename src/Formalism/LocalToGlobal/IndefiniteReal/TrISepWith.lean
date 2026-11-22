module

public import Mathlib
public import Formalism.LocalToGlobal.HilbertRowConditions.ColumnsFunctionAtSubspaces
public import Formalism.LocalToGlobal.IndefiniteReal.PrimitivePackageFullHecke
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Formalism.LocalToGlobal.IndefiniteReal.SpOfRwRange
public import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.SignsG
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.STiesR
public import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.FramesOK
public import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.NormalFrameClauses
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.RatDatOfReal
public import Formalism.LocalToGlobal.IndefiniteReal.AutomorphicEvaluation
public import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.UnipotentInLevelSubgroup

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR.Links Formalism.IndefR.Cx

namespace Formalism.IndefR

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}

def faceT (P : RowSideFamily ex) (Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs))
    (Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)) (Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3) :
    Face3 D P.A3 :=
  ⟨P.P0, P.ψ0, P.Ps, P.ψs, Dcf, Spf, Zscf⟩

def TrISepWith {G Pl0 I0 T : Type} [Group G] [Fintype G] (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m)
    (tr : Fin D.R.m → (I0 × List ℕ → D.what₂.LL) → I0 × List ℕ → D.what₂.LL) : Prop :=
  ∀ (j : Fin D.R.m), ∀ p ∈ (A3.fam3.RI A3.fam3.F.μ0).ixFin3 A3.fam3.F.X,
    ∀ p' ∈ (A3.fam3.RI A3.fam3.F.μ0).ixFin3 A3.fam3.F.X,
    (∃ k : A3.okI A3.A.μ0 × List ℕ, p.2 (k.1.1, k.2) ≠ p'.2 (k.1.1, k.2)) →
      ∃ k : A3.okI A3.A.μ0 × List ℕ, tr j p.2 (k.1.1, k.2) ≠ tr j p'.2 (k.1.1, k.2)

open Classical in
def hkCan {G Pl0 I0 T : Type} [Group G] [Fintype G] (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) : HkDat3 A3 where
  Hk := A3.fam3.base3.Ix
  ev p q := if p = q then 1 else 0
  ev_inj p p' h := by
    have h2 := congrFun h p
    dsimp only at h2
    rw [if_pos rfl] at h2
    by_contra hne
    rw [if_neg (fun h' => hne h'.symm)] at h2
    exact one_ne_zero h2

def errCan {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs} (S : IndefData Df)
    (F0 : HeightOneSpectrum (𝓞 K) → Bs.J → ℝ) (w : HeightOneSpectrum (𝓞 K)) : ℝ :=
  max 0 ((∑ j', ((S.Iw j' (S.μ w) w : ℝ) + (S.Iw j' (S.μ w) (Formalism.DivisionValues.conjPl w) : ℝ))) / (S.D : ℝ) -
      ∑ j', 2 * ((Formalism.EigenvalueLevelCeiling.ramw w : ℝ) * F0 w j') - (Formalism.EigenvalueLevelCeiling.ramw w : ℝ) * (2 / (Formalism.EigenvalueLevelCeiling.plc w : ℝ) ^ 2)) /
    ((Formalism.EigenvalueLevelCeiling.ramw w : ℝ) * (Fintype.card Bs.J : ℝ))

def seeKS (X : Formalism.L2.SG.HidaSetting.HidaSetting D) : Set X.B.I.GA := {x | x.1 = 1 ∧ x.2 ∈ X.K2}

def seeChiS (X : Formalism.L2.SG.HidaSetting.HidaSetting D) : X.B.I.GA → ℂ := fun x => star (X.chi2 x.2)

namespace RealT

variable {Rc : Formalism.L2.RecT ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
  {S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  (R : RealT Rc P Dcf Spf Zscf S Ks)

end RealT

end Formalism.IndefR
