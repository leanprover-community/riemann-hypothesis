module

public import Formalism.LocalToGlobal.GroupLattices.CloudFilling.TauTopPlacesIff
public import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.PosCompatOfBase
public import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.RepTie
public import Formalism.LocalRingCardinality.DataExtra
public import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem

@[expose] public section

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.UG Formalism.MainNotions.G Formalism.FrobeniusOrbits
open scoped TensorProduct

namespace Formalism.L2.G

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure LocPack (D : D7) (u : D.what₂.Word)
    (Lc : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u)) (p : ℕ) where
  W : Type
  Qq : Type
  O : Type
  Kf : Type
  [cW : CommRing W]
  [dW : IsDomain W]
  [vW : IsDiscreteValuationRing W]
  [fQ : Field Qq]
  [aW : Algebra W Qq]
  [cO : CommRing O]
  [dO : IsDomain O]
  [vO : IsDiscreteValuationRing O]
  [fK : Field Kf]
  [aO : Algebra O Kf]
  ι : Qq →+* Kf
  σ : Qq ≃+* Qq
  j : W →+* O
  w : O
  hS : HidaSetting p (orderOf (zH D.R.toFrame (hP D p))) W Qq O Kf ι σ j w
  I : LocId Lc p (nOrb (zH D.R.toFrame (hP D p))) W Qq
  ψ : Formalism.L2.Herm.awayFrom₂ Lc p →* Oˣ

attribute [instance] LocPack.cW LocPack.dW LocPack.vW LocPack.fQ LocPack.aW LocPack.cO LocPack.dO LocPack.vO LocPack.fK
  LocPack.aO

def rSc (sc : Scale) (k p : ℕ) : ℕ := if (p : ℝ) < sc.p0 k then rG sc else 1

theorem rRec_eq {D : D7} (L : SizeData₂ D) (p : ℕ) : rRec L p = rSc L.sc D.R.k p := rfl

def epSc (R : Ranks) (sc : Scale) (Ce : ℝ) (p : ℕ) : ℕ := ⌈Ce * (R.f : ℝ) * (R.k : ℝ) ^ 2 * Real.logb p sc.a⌉₊

abbrev LocPack.gat {D : D7} {u : D.what₂.Word}
    {Lc : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u)} {p : ℕ} (X : LocPack D u Lc p)
    (r e : ℕ) : GAtP p :=
  gatRec D u (D.R.iota (hP D p)) X.hS r Lc X.I X.ψ (repP Lc p) e

def LocPack.posOK {D : D7} {u : D.what₂.Word}
    {Lc : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u)} {p : ℕ} [Fact p.Prime]
    (X : LocPack D u Lc p) (iK : X.Kf →+* ℂ_[p])
    (lam : (algebraicClosure ℚ ℂ) →+* ℂ_[p]) : Prop :=
  PosCompat D.host (D.R.iota (hP D p)) X.ι X.σ X.I.iw iK lam

variable (D : D7) (sc : Scale) (Ce : ℝ)
  (Lc : ∀ u, ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
  (X : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    LocPack D u (Lc u) (D.what₂.places.resChar w))
  (hd : ∀ u w h, ((X u w h).gat (rSc sc D.R.k (D.what₂.places.resChar w)) (epSc D.R sc Ce (D.what₂.places.resChar w))).d =
    Module.finrank ℂ (D.mem u).A.Mu0)

def recG : D7 :=
  { D with
    gat := fun u w h => (X u w h).gat (rSc sc D.R.k (D.what₂.places.resChar w)) (epSc D.R sc Ce (D.what₂.places.resChar w))
    gat_d := hd }

def gatTiesG : GatTies (recG D sc Ce Lc X hd) where
  gat_k := fun _ _ _ => k_pred D.R
  gat_n := fun (u : D.what₂.Word) (w : D.what₂.places.Pl)
      (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) v (P : Ideal (𝓞 D.host.E)) (hP : P.IsPrime)
      (hL : P.LiesOver (Ideal.span {((D.what₂.places.resChar w : ℕ) : ℤ)})) τ hτ =>
    haveI := hP
    haveI := hL
    gatRec_n_frob D u h (X u w h).hS _ (Lc u) (X u w h).I (X u w h).ψ (repP (Lc u) _) _ v P τ hτ
  gat_pos := fun (u : D.what₂.Word) (w : D.what₂.places.Pl)
      (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) =>
    gatRec_pos D u _ (X u w h).hS (rSc sc D.R.k (D.what₂.places.resChar w)) (Lc u) (X u w h).I (X u w h).ψ (repP (Lc u) _)
      (epSc D.R sc Ce (D.what₂.places.resChar w))
  gat_step := fun (u : D.what₂.Word) (w : D.what₂.places.Pl)
      (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) v s (P : Ideal (𝓞 D.host.E)) (hP : P.IsPrime)
      (hL : P.LiesOver (Ideal.span {((D.what₂.places.resChar w : ℕ) : ℤ)})) τ hτ =>
    haveI := hP
    haveI := hL
    gatRec_step_frob D u h (X u w h).hS _ (Lc u) (X u w h).I (X u w h).ψ (repP (Lc u) _) _ v s P τ hτ
  gat_lam := fun _ _ _ _ _ _ => rfl

variable (L : SizeData₂ (recG D sc Ce Lc X hd)) (P : ParameterChoice' (recG D sc Ce Lc X hd) L)

def levTieG (u : D.what₂.Word) (w : D.what₂.places.Pl) (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    Formalism.L2.Herm.GLevTie (Lc u) ((recG D sc Ce Lc X hd).gat u w h) :=
  gatRecP_lev D u _ (X u w h).hS _ (Lc u) (X u w h).I (X u w h).ψ _

end Formalism.L2.G
