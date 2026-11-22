module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsetTwistExceptionalPlaces
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RatInEig
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyPtsOfReading
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LabConj

@[expose] public section

noncomputable section

namespace GlobalTheory.HeightCounting

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
  Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option genInjectivity false
set_option genSizeOfSpec false
set_option maxHeartbeats 1000000

def Reads {D : D7} (X : NExpTied D) (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
    (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (hA : NX.AdmTw D i k Q ψ)
    (e : FractionRing (D.ntw.Ok i k) →+* ℂ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (r : D.nexp.MtV i j b k Q ψ → GAf D.host.E D.R.nV → V) : Prop :=
  ∃ ω : (X.mtV i j b k Q ψ h1 h2 hA).W →ₛₗ[e] V, Function.Injective ω ∧
    ∀ f g, r f g = ω (((X.mtV i j b k Q ψ h1 h2 hA).real f).1 g)

def plsOf {D : D7} (X : NExpTied D) (i : D.ntw.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host))
    (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (hA : NX.AdmTw D i k Q ψ) :
    Finset (PlE D.host) × Finset (PlE D.host) := ((X.mtV i j b k Q ψ h1 h2 hA).QP, (X.mtV i j b k Q ψ h1 h2 hA).DP)

structure ExpRel {D : D7} (L : LocAll (lay0 D)) (X : NExpTied D) (X' : NExpTied (withLoc L)) : Prop where
  tau : TauTrue X → TauTrue X'
  pl : ∀ i j b k Q ψ h1 h2 hA, plsOf X' i j b k Q ψ h1 h2 hA = plsOf X i j b k Q ψ h1 h2 hA
  reads : ∀ i j b k Q ψ h1 h2 hA e (V : Type) [AddCommGroup V] [Module ℂ V] r,
    Reads X i j b k Q ψ h1 h2 hA e V r → Reads X' i j b k Q ψ h1 h2 hA e V r

section Rows

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {C : Formalism.L2.Pj.CoreJ D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat3 D A3 C.Q.c.F}
  {F : Face3 D A3} {X0 : BaseLevelRowSide D} (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) {cf : CharFrame D}

def repOf : D.what₂.FT → NG.FinTyp D.host.E D.R.r := fun σ => principalLevelFrame.rowRepR R.θ (Y.eFT σ)

structure InMt (cf : CharFrame D) (xi : D.what₂.Tup → HChar D.host.E) (Q : D.what₂.places.Pl → Finset (PlE D.host)) : Type 1 where
  M : MtFam D
  ad : MtAd Y M
  mt : MtInput D M (fun μ j => cf.mu0 j * xi μ) Q

structure InRat : Type 1 where
  kKs : C.Q.c.F →+* ↥D.LL0
  hk : ∀ x : C.Q.c.F, ((kKs x : ↥D.LL0) : D.what₂.LL) = algebraMap C.Q.c.F D.what₂.LL x
  In : RatIn D (ratDatR R cG kKs hk)
  rat : RatAd Y cG kKs hk In

variable {Y cG}

abbrev InRat.S (n : InRat Y cG) : RatDat D.ntw := ratDatR R cG n.kKs n.hk

variable (g : GlobalTheory.RealGeo.GeoHalf C R.toRealDat fun _ => 1)

variable {g}

end Rows

end GlobalTheory.HeightCounting

end
