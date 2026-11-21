import Formalism.SharpRestriction.InertJacobiLevels.GaugeExists
import Formalism.SharpRestriction.InertJacobiLevels.ExtraGatC
import Formalism.LocalRingCardinality.KernelPlaceMeanBound
import Formalism.LocalRingCardinality.SpanPowerMembership.WithSeenTauOf
import Formalism.LocalRingCardinality.SpanPowerMembership.TiesGen
import Formalism.LocalRingCardinality.SpanPowerMembership.DivXExample

section
noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.BasicNotions.DV NumberField

def logOmV (D : D7) (dl : ℝ) : ℝ := Real.eulerMascheroniConstant + Real.log (Real.pi / D.host.v) - dl

def LaV (D : D7) (sc : Scale) : ℝ := Real.log (sc.a * D.host.rdE)

def LprimeV (D : D7) (sc : Scale) : ℝ :=
  Real.log (sc.b * D.host.rdE * ((D.host.g 0 : ℝ) * D.host.g 1) * D.R.nV)

def kerPlaceV (D : D7) (dl : ℝ) (u : D.what₂.Word) (j : ℕ) (τ : D.what₂.Tau) : ℝ :=
  (∑ i ∈ Finset.range (D.R.N (j - 1)), phF (nuRow D u j τ i)) -
    (∑ i ∈ Finset.range (D.R.N (j - 1)), nuRow D u j τ i) * logOmV D dl

def SZbKV (D : D7) (sc : Scale) (dl C : ℝ) (u : D.what₂.Word) (j : ℕ) : ℝ :=
  (∑ ρ : D.what₂.Tau, kerPlaceV D dl u j ρ) +
    C * (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ 2 * LaV D sc +
    C * (D.R.f : ℝ) * (D.R.m : ℝ) ^ 3 * (D.R.N D.R.m : ℝ) ^ 2 * sc.L

def InertJacobiLowerValue (D : D7) (sc : Scale) (C : ℝ) (j : ℕ) : ℝ :=
  (∑ ρ : D.what₂.Tau, logHook (D.R.sigW j).1 (aPlus D j ρ)) -
    C * (D.R.f : ℝ) * (D.R.nV : ℝ) ^ 2 * LprimeV D sc

def SZbPV (D : D7) (sc : Scale) (aT : D.host.TT → ℤ) (η Sc C : ℝ) (u : D.what₂.Word) : ℝ :=
  -(∑ t : D.host.TT, (aT t : ℝ) * Real.log ((D.mem u).A.T : ℝ)) +
    C * ((D.host.TT.card : ℝ) * sc.b' * (D.R.N D.R.m : ℝ) +
      (D.R.f : ℝ) * ((D.R.m : ℝ) * η + Sc) * (D.R.N D.R.m : ℝ) +
      (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ 2) * LaV D sc

def hVal (D : D7) (sc : Scale) (aT : D.host.TT → ℤ) (η Sc dl C : ℝ) (u : D.what₂.Word) : ℝ :=
  SZbPV D sc aT η Sc C u + (∑ j ∈ SizeData₂.lifts D, SZbKV D sc dl C u j) - ∑ j ∈ SizeData₂.lifts D, InertJacobiLowerValue D sc C j



end Formalism.MainNotions.Inhab

end
end

section
noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.MainNotions NumberField IsDedekindDomain

structure Shape0 (D : D7) : Prop where
  mult : ∀ μ j, Subsingleton (D.what₂.Mult μ j)
  amb : ∀ μ, Subsingleton (D.what₂.Amb μ)
  mtL : ∀ μ j, Subsingleton (D.what₂.MtL μ j)
  mj : ∀ j, Subsingleton (D.what₂.Mj j)
  ee0 : Subsingleton D.what₂.EE0
  rr : Subsingleton D.div.RR.V
  nu : ∀ u, Subsingleton (D.div.Nu u).V
  lat : ∀ u j, Subsingleton ((D.fm u).lat j).V
  yTw : ∀ u μ i, IsEmpty ((D.chTw u μ).Y i)
  clsTw : ∀ u μ j, IsEmpty ((D.chTw u μ).cls (j + 1))
  mtV : ∀ i j b k Q ψ, Subsingleton (D.nexp.MtV i j b k Q ψ)
  fmN : ∀ i j b, Subsingleton (D.nexp.Fm i j b)
  ll0 : ∀ x : D.what₂.LL, x ∈ D.LL0
  Ij0 : ∀ μ j w, D.what₂.Ij μ j w = 0
  jw0 : ∀ μ j w, D.what₂.jw μ j w = 0
  drows : D.what₂.Drows = 0
  dgam : ∀ u μ, (D.chTw u μ).DGam = (D.mem D.u₀).C.DGam
  mink : DGamMink D
  loc : IsEmpty D.nd.Loc
  cls0 : ∀ u μ, Nonempty ((D.mem u).C.cls 0 ≃ (D.chTw u μ).cls 0)

variable {D : D7}

theorem Shape0.withGat (S : Shape0 D) (h0 : ∀ u, Module.finrank ℂ (D.mem u).A.Mu0 = 0)
    (rOf : D.what₂.Word → ℕ → ℕ) (eOf : ℕ → ℕ) (bs : D.what₂.Word → ℕ → Set ↥(D.R.Psi)) :
    Shape (withGatC D h0 rOf eOf bs) where
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
  mtV := S.mtV
  fmN := S.fmN
  ll0 := S.ll0
  Ij0 := S.Ij0
  jw0 := S.jw0
  drows := S.drows
  dgam := S.dgam
  mink := S.mink
  loc := S.loc
  gatM := withGatC_M D h0 rOf eOf bs
  gatComp := fun u w _ => S.cls0 u (D.what₂.muAt w)
  gatTr := withGatC_trans D h0 rOf eOf bs

theorem Shape0.withSeen (S : Shape0 D) (seen tau) : Shape0 (withSeen D seen tau) where
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
  mtV := S.mtV
  fmN := S.fmN
  ll0 := S.ll0
  Ij0 := S.Ij0
  jw0 := S.jw0
  drows := S.drows
  dgam := S.dgam
  mink := S.mink
  loc := S.loc
  cls0 := S.cls0

structure LevGapD (D : D7) where
  lev : LevelData D
  errX : ErrX D
  piG_lev : PiGLevel D lev errX
  piT_lev : PiTLevel D lev errX
  tau : ∀ u, D.what₂.places.Pl → ((D.mem u).A.vT ≃ D.what₂.Tau)
  tau_def : ∀ u (w : D.what₂.places.Pl), D.what₂.places.resChar w = (D.mem u).A.T → ∀ (v : (D.mem u).A.vT)
    (x : 𝓞 D.host.F), x ∈ (errX.vPl u v).asIdeal ↔
      (0 : WithTop ℤ) < D.what₂.places.val w (tauLL D (tau u w v) (algebraMap D.host.F D.host.E (x : D.host.F)))

open Classical in

def seenOf (D : D7) (X : ErrX D) : D.what₂.Word → D.what₂.places.Pl → Bool :=
  fun u w => decide (∀ τ : D.what₂.Tau, (0 : WithTop ℤ) < D.what₂.places.val w (tauLL D τ (X.piT u : D.host.E)))

def LevGapD.recS (G : LevGapD D) : D7 := withSeen D (seenOf D G.errX) G.tau

def errXSeen (X : ErrX D) (seen tau) : ErrX (withSeen D seen tau) where
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

def LevGapD.le (G : LevGapD D) : LevErr G.recS where
  lev := G.lev
  errX := errXSeen G.errX _ _
  piG_lev := G.piG_lev
  piT_lev := G.piT_lev
  seen := fun u w _ => by
    show seenOf D G.errX u w = true ↔ _
    unfold seenOf
    rw [decide_eq_true_iff]
    rfl
  tauOf := G.tau_def

section LevelValuationRings

variable (h0 : ∀ u, Module.finrank ℂ (D.mem u).A.Mu0 = 0)
    (rOf : D.what₂.Word → ℕ → ℕ) (eOf : ℕ → ℕ) (bs : D.what₂.Word → ℕ → Set ↥(D.R.Psi))

def errXGat (X : ErrX D) : ErrX (withGatC D h0 rOf eOf bs) where
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

def LevErr.withGat (le : LevErr D) : LevErr (withGatC D h0 rOf eOf bs) where
  lev := le.lev
  errX := errXGat h0 rOf eOf bs le.errX
  piG_lev := le.piG_lev
  piT_lev := le.piT_lev
  seen := le.seen
  tauOf := le.tauOf

variable (B : D.what₂.Word → ℕ → Set (G.HH D))

theorem Shape0.withGatB (S : Shape0 D) : Shape (withGatCB D h0 rOf eOf B) := S.withGat h0 rOf eOf _

def LevErr.withGatB (le : LevErr D) : LevErr (withGatCB D h0 rOf eOf B) := LevErr.withGat h0 rOf eOf _ le

end LevelValuationRings

theorem LevGapD.shape0 (large₂ : LevGapD D) (S : Shape0 D) : Shape0 large₂.recS := S.withSeen _ _

def ServedGap : Prop :=
  ∀ (D : D7), Function.Bijective D.embE → ∀ (h0 : ∀ u, Module.finrank ℂ (D.mem u).A.Mu0 = 0)
    (rOf : D.what₂.Word → ℕ → ℕ) (eOf : ℕ → ℕ) (bs : D.what₂.Word → ℕ → Set ↥(D.R.Psi))
    (u : D.what₂.Word) (w : D.what₂.places.Pl) (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    haveI : Fact ((withGatC D h0 rOf eOf bs).what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
    Nonempty (ServedEmb (withGatC D h0 rOf eOf bs) u w h)

def GaugeGap : Prop :=
  ∀ (R : Ranks) (H : Host R) (sp : @Spaces R H.F H.E _ _ _ _ H.cmStar _), GaugeExists H sp

end Formalism.MainNotions.Inhab

end
end

section
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
end
