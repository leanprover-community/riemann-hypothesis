module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsetTwistExceptionalPlaces
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyPtsOfReading
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LabConj
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyAllIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaOfOfIsCharLab
public import Formalism.LocalToGlobal.UnitaryNorms.MemFIffReal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
public import Lean.Meta.Injective

@[expose] public section

noncomputable section

namespace GlobalTheory.HeightCounting

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
  Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar


set_option genInjectivity false
set_option genSizeOfSpec false


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

structure StA (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (cf : CharFrame D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r) : Type 1 where
  host : HostTied D
  jE : D.host.E →+* Qb
  frame : ∀ x, jE x = host.fr.j x
  A : SideA D cf jE
  cg : CGTrue hL D A.wdT
  au : AUTrue hL D A.wdT A.au
  row : RowTrue hL D rep (fun σ w => A.wdT.e w (A.row.locR σ w)) A.row.satR
  fr : OmFrame D
  fr_jE : fr.jE = jE
  pht : PhtOn A.wd fr fun _ _ _ _ => True
  depth : RowDepth D rep
  elem : Elem D
  val : ValLL0 D cf
  labc : LabConj D A.wdT
  zeta : ∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; A.grp.ζ k = (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen
  omax : Function.Injective D.what₂.OtoLL ∧ ∃ F : Subfield D.what₂.LL, ∀ x, x ∈ D.what₂.OtoLL.range ↔ x ∈ F ∧ IsIntegral ℤ x

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

structure SettingsFormsState (a : StA hL D cf (repOf Y)) (n : InRat Y cG)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) : Type 1 where
  Bs : SideB D cf a.A.row (lowAll D) Pq n.S n.In.hL n.In.eig n.In.θ
  Sb_le : ∀ i, n.In.Sb ⊆ D.ntw.S0 i
  rootsOfUnityRing_le_wittIntegers : ∀ i, OverSet D (D.ntw.S0 i) (insert (D.ntw.l i) (lowAll D))
  lam : ∃ Z : GlobalTheory.LamTie.LamDat D, Z.Ok ∧ Z.Teich ∧ Z.C = cf ∧ Z.q0 = AbsolutelyIrreducibleSpan.q0 D ∧ GlobalTheory.LamTie.IsLamTieFull D.ntw Z

variable (g : GlobalTheory.RealGeo.GeoHalf C R.toRealDat fun _ => 1)

structure SeriesState (a : StA hL D cf (repOf Y)) (n : InRat Y cG) (PV : ∀ i : Fin D.R.m, principalLevelFrame.RowPsi (Vc D i) D.R.nV)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) : Type 1 extends SettingsFormsState a n Pq where
  YS : NExpRealS R cG n.S
  eF : YS.eF = Bs.eF
  fi : ∀ i x, HEq ((YS.fi i).e x) x
  ser : SerAt YS g.v₀ Bs.exp PV cf Pq
  tau : TauTrue Bs.exp

structure ModuliPointsState (a : StA hL D cf (repOf Y)) (n : InRat Y cG) (PV : ∀ i : Fin D.R.m, principalLevelFrame.RowPsi (Vc D i) D.R.nV)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) : Type 1 extends SeriesState g a n PV Pq where
  geo : Nonempty (GlobalTheory.GeoTie.ThetaTie YS g.fw D.nth)

variable {g}

structure StC {a : StA hL D cf (repOf Y)} {n : InRat Y cG} {xi : D.what₂.Tup → HChar D.host.E}
    {Q : D.what₂.places.Pl → Finset (PlE D.host)} (m : InMt Y cf xi Q)
    {Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host} (b : ModuliPointsState g a n m.ad.PV Pq)
    (k : D.what₂.places.Pl → ℕ) (psi : D.what₂.places.Pl → HChar D.host.E) : Type 1 where
  ch : NChoice D
  tp : TupTied D cf ch
  xi_eq : tp.xi = xi
  psi_eq : tp.psi = psi
  Q_eq : ch.Q = Q
  k_eq : ∀ w, TwistedAt D w → ch.k' w = k w
  side : ChoiceSide D cf m.M b.Bs.exp ch tp
  ok : ∀ w, TwistedAt D w → IntegralHeckeForms.TwOK (ch.twI w) (ch.k' w) (ch.Q w) ((ch.psi' w).comp (D.ntw.art (ch.twI w) (ch.Q w)))
  th : EMtTheta Y b.YS ch

end Rows


end GlobalTheory.HeightCounting

end
