module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CGTrue
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro

@[expose] public section

noncomputable section

namespace GlobalTheory.TwInputs

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX ReciprocityTheory.Gal
  NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.HeightCounting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure TwJoin (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (nch : NChoice D) (xd : ThData D) (first : Prop) {G : Type}
    [iG : Group G] [fG : Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {C : Formalism.L2.Pj.CoreJ D} [aC : Algebra C.Q.c.F D.what₂.LL]
    (R : RealDat3 D A3 C.Q.c.F) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd)
    (geo : GlobalTheory.RealGeo.GeoHalf C R.toRealDat fun _ => 1) (S : RatDat D.ntw) (YS : NExpRealS R cG S)
    (cf : CharFrame D) : Type 1 where
  X : RealSide D
  Γ_eq : X.Γ = G
  grp_eq : HEq X.grp iG
  fin_eq : HEq X.fin fG
  Pl0_eq : X.Pl0 = Pl0
  I0_eq : X.I0 = I0
  T_eq : X.T = T
  core_eq : X.core = C
  alg_eq : HEq X.alg aC
  R_eq : HEq X.R R
  F_eq : HEq X.F F
  cG_eq : HEq X.cG cG
  geo_eq : HEq X.geo geo
  A3_eq : HEq X.A3 A3
  Y : SerSide X (twEOf xd)
  S_eq : Y.S = S
  YS_eq : HEq Y.YS YS
  gal : GalSide D
  cf_eq : gal.cf = cf
  lam_eq : gal.lam.C = cf
  C_eq : X.R.C = cf
  field : FieldOk X
  cg : CGTrue hL D gal.wd
  base : first → ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → BaseTup Y (nch.twI w)

theorem TwJoin.Sb_eq {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} {nch : NChoice D} {xd : ThData D} {first : Prop} {G : Type}
    [iG : Group G] [fG : Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {C : Formalism.L2.Pj.CoreJ D}
    [aC : Algebra C.Q.c.F D.what₂.LL] {R : RealDat3 D A3 C.Q.c.F} {F : Face3 D A3} {cG : G0 R.Pg D.R.r ≃* G0g D.nd}
    {geo : GlobalTheory.RealGeo.GeoHalf C R.toRealDat fun _ => 1} {S : RatDat D.ntw} {YS : NExpRealS R cG S}
    {cf : CharFrame D} (a : TwJoin hL D nch xd first R F cG geo S YS cf) : a.X.R.Sb = R.Sb := by
  obtain ⟨X, h1, h2, h3, h4, h5, h6, h7, h8, hR, -, -, -, hA, -⟩ := a
  cases X
  dsimp only at h1 h2 h3 h4 h5 h6 h7 h8 hR hA ⊢
  subst h1 h4 h5 h6 h7
  cases h2; cases h3; cases h8; cases hA; cases hR
  rfl

end GlobalTheory.TwInputs

end
