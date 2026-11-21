import Formalism.SharpRestriction.InertJacobiLevels.ExtraMods
import Formalism.LocalRingCardinality.SpanPowerMembership.TiesGen
import Formalism.LocalRingCardinality.SpanPowerMembership.DivXExample

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.MainNotions NumberField IsDedekindDomain

variable {D : D7}

theorem Shape0.withTw (S : Shape0 D) (W : TwGap D) (hV : ∀ i j b k Q ψ, Subsingleton (W.nexp.MtV i j b k Q ψ))
    (hF : ∀ i j b, Subsingleton (W.nexp.Fm i j b)) : Shape0 (withTw D W) where
  mult := S.mult
  amb := S.amb
  mtL := S.mtL
  mj := S.mj
  ee0 := S.ee0
  rr := S.rr
  nu := S.nu
  lat := S.lat
  yTw := S.yTw
  clsTw := S.clsTw
  mtV := hV
  fmN := hF
  ll0 := S.ll0
  Ij0 := S.Ij0
  jw0 := S.jw0
  drows := S.drows
  dgam := S.dgam
  mink := S.mink
  loc := S.loc
  cls0 := S.cls0

def errXTw (X : ErrX D) (W : TwGap D) : ErrX (withTw D W) where
  piG := X.piG
  piG_K := X.piG_K
  piG_norm := X.piG_norm
  piT := X.piT
  piT_K := X.piT_K
  piT_norm := X.piT_norm
  piT_cong := X.piT_cong
  vPl := X.vPl
  vPl_inj := X.vPl_inj
  norm_mem_place_ideal := X.norm_mem_place_ideal

def LevGapD.withTw (G : LevGapD D) (W : TwGap D) : LevGapD (withTw D W) where
  lev := G.lev
  errX := errXTw G.errX W
  piG_lev := G.piG_lev
  piT_lev := G.piT_lev
  tau := G.tau
  tau_def := G.tau_def

section Rec

variable (D1 : D7) (W : TwGap D1) (large₂ : LevGapD D1) (h0 : ∀ u, Module.finrank ℂ (D1.mem u).A.Mu0 = 0)
  (rOf : D1.what₂.Word → ℕ → ℕ) (eOf : ℕ → ℕ) (B : D1.what₂.Word → ℕ → Set (G.HH D1))

def recX : D7 := withGatCB (large₂.withTw W).recS h0 rOf eOf B

def recX_gatT : GatTies (recX D1 W large₂ h0 rOf eOf B) := gatTiesCB (large₂.withTw W).recS h0 rOf eOf B

theorem recX_shape (S : Shape0 D1) (hV : ∀ i j b k Q ψ, Subsingleton (W.nexp.MtV i j b k Q ψ))
    (hF : ∀ i j b, Subsingleton (W.nexp.Fm i j b)) : Shape (recX D1 W large₂ h0 rOf eOf B) :=
  Shape0.withGatB (D := (large₂.withTw W).recS) h0 rOf eOf B ((large₂.withTw W).shape0 (S.withTw W hV hF))

def recX_le : LevErr (recX D1 W large₂ h0 rOf eOf B) :=
  LevErr.withGatB (D := (large₂.withTw W).recS) h0 rOf eOf B (large₂.withTw W).le

theorem recX_ties (t : Ties (withTw D1 W)) : Ties (recX D1 W large₂ h0 rOf eOf B) :=
  { cdScale_tie := t.cdScale_tie
    dsig_tie := t.dsig_tie
    bu_def := t.bu_def
    tw_cover := t.tw_cover
    baseField_isGalois := t.baseField_isGalois
    ft_occ := t.ft_occ }








def recX_served (hS : ServedGap) (hb : Function.Bijective D1.embE) (u : (recX D1 W large₂ h0 rOf eOf B).what₂.Word)
    (w : (recX D1 W large₂ h0 rOf eOf B).what₂.places.Pl)
    (h : GIdx (recX D1 W large₂ h0 rOf eOf B).host ((recX D1 W large₂ h0 rOf eOf B).mem u).A.T
      ((recX D1 W large₂ h0 rOf eOf B).what₂.places.resChar w)) :
    haveI : Fact ((recX D1 W large₂ h0 rOf eOf B).what₂.places.resChar w).Prime :=
      ⟨(recX D1 W large₂ h0 rOf eOf B).what₂.places.resChar_prime w⟩
    ServedEmb (recX D1 W large₂ h0 rOf eOf B) u w h :=
  (hS (large₂.withTw W).recS hb h0 rOf eOf (fun u p => tau1P D1.R.toFrame '' B u p) u w h).some

def recX_X (S : Shape0 D1) : DivX (recX D1 W large₂ h0 rOf eOf B) := divXExample _ S.drows S.mj

theorem recX_mjH (S : Shape0 D1) (j : ℕ) : Subsingleton ((recX_X D1 W large₂ h0 rOf eOf B S).MjH j).V :=
  inferInstanceAs (Subsingleton (zeroHLat _).V)



set_option maxHeartbeats 2000000 in
theorem recX_hVal (sc : Scale) (aT : D1.host.TT → ℤ) (η Sc dl C : ℝ) (u) :
    hVal (recX D1 W large₂ h0 rOf eOf B) sc aT η Sc dl C u = hVal D1 sc aT η Sc dl C u := rfl

end Rec

end Formalism.MainNotions.Inhab

end
