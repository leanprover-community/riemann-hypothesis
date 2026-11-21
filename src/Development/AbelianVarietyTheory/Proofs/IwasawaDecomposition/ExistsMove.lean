import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RealMoveOfParts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DofOTw
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChoiceOfLocalAdmissible
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesOfLifts
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OmPinsTr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RealMoveOfLink

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
open GlobalTheory.HeightCounting.SerMove

open GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.R3.Rw.StateChecks

namespace GlobalTheory.HeightCounting.SerMove.ReGeo

variable {B : Base} {f : Top.Fr B.toPre} {T : TwDat B} {w : ColW B f T} {hX : B.fields.Ok} {Wt : Set B.places.Pl}

set_option maxHeartbeats 4000000 in

theorem geo_copy {Z Z' : w.Lt} (z₀ : Dat (w.st Z) w.I hX T Wt) (z : Dat (w.st Z') w.I hX T Wt) (h1 : z.Xg = z₀.Xg)
    (h2 : z.tr = z₀.tr) (h3 : HEq z.core (coreJ (a := Z) Z' z₀.core)) (h4 : HEq z.R (real3 (a := Z) Z' (iK := z₀.alg) z₀.R))
    (hg : GlobalTheory.RealGeo.InGeo z₀.geo) :
    ∃ g : GlobalTheory.RealGeo.GeoHalf z.core z.R.toRealDat (fun _ => 1), GlobalTheory.RealGeo.InGeo g ∧
      (∀ {B' : Base} {f' : Top.Fr B'.toPre} {T' : TwDat B'} {w' : ColW B' f' T'} {Z'' : w'.Lt} {hX' : B'.fields.Ok}
        {Wt' : Set B'.places.Pl} (z' : Dat (w'.st Z'') w'.I hX' T' Wt'), ExtN z₀ z' → ExtN { z with geo := g } z') ∧
      (∀ {B' : Base} {f' : Top.Fr B'.toPre} {T' : TwDat B'} {w' : ColW B' f' T'} {Z'' : w'.Lt} {hX' : B'.fields.Ok}
        {Wt' : Set B'.places.Pl} (z' : Dat (w'.st Z'') w'.I hX' T' Wt'), ExtN z' z₀ → ExtN z' { z with geo := g }) := by
  obtain @⟨Xg, tr, core, al, alg_eq, R, cG, geo, pins, lev, idG, good, mu, l1, l2⟩ := z
  dsimp only at h1 h2 h3 h4 ⊢
  subst h1 h2
  obtain rfl : core = coreJ (a := Z) Z' z₀.core := eq_of_heq h3
  have e : al = (by with_unfolding_all exact ((alg (a := Z) Z' z₀.alg) :)) := by
    refine Algebra.algebra_ext _ _ fun y => B.embLL.injective ?_
    exact (alg_eq y).trans ((by with_unfolding_all exact ((z₀.alg_eq ((by with_unfolding_all exact (y :)))).symm :)))
  subst e
  obtain rfl : R = cpR (a := Z) Z' z₀ := eq_of_heq (h4.trans ((by with_unfolding_all exact ((HEq.refl (cpR (a := Z) Z' z₀)) :))))
  refine ⟨(by with_unfolding_all exact ((geoHalf (a := Z) Z' (iK := z₀.alg) z₀.geo) :)), (by with_unfolding_all exact ((inGeo_tr (a := Z) Z' (iK := z₀.alg) hg) :)), ?_, ?_⟩
  · intro B' f' T' w' Z'' hX' Wt' z' e
    exact
      { H := (by with_unfolding_all exact (e.H :))
        l := (by with_unfolding_all exact (e.l :))
        c := (by with_unfolding_all exact (e.c :))
        Dw := (by with_unfolding_all exact (e.Dw :))
        Xo := (by with_unfolding_all exact (e.Xo :))
        U := (by with_unfolding_all exact (e.U :))
        V := (by with_unfolding_all exact (e.V :))
        dict := (by with_unfolding_all exact (e.dict :))
        mu := (by with_unfolding_all exact (e.mu :))
        Kf := (by with_unfolding_all exact (e.Kf :))
        cE := (by with_unfolding_all exact (e.cE :))
        chiW := (by with_unfolding_all exact (e.chiW :))
        x₀ := (by with_unfolding_all exact (e.x₀ :))
        iota := (by with_unfolding_all exact (e.iota :))
        ψ := (by with_unfolding_all exact (e.ψ :))
        θ := (by with_unfolding_all exact (e.θ :))
        βW := (by with_unfolding_all exact (e.βW :))
        βY := (by with_unfolding_all exact (e.βY :))
        nW := (by with_unfolding_all exact (e.nW :))
        βV := (by with_unfolding_all exact (e.βV :))
        ΛV := (by with_unfolding_all exact (e.ΛV :))
        ΛW := (by with_unfolding_all exact (e.ΛW :))
        Pg := (by with_unfolding_all exact (e.Pg :))
        eG := (by with_unfolding_all exact (e.eG :))
        Sb := (by with_unfolding_all exact (e.Sb :))
        BV := (by with_unfolding_all exact (e.BV :))
        MW := (by with_unfolding_all exact (e.MW :))
        forms := (by with_unfolding_all exact (e.forms :))
        cV := (by with_unfolding_all exact (e.cV :))
        pb := (by with_unfolding_all exact (e.pb :))
        ΛY := (by with_unfolding_all exact (e.ΛY :))
        κ := (by with_unfolding_all exact (e.κ :))
        ref := (by with_unfolding_all exact (e.ref :))
        jL := (by with_unfolding_all exact (e.jL :)) }
  · intro B' f' T' w' Z'' hX' Wt' z' e
    exact
      { H := (by with_unfolding_all exact (e.H :))
        l := (by with_unfolding_all exact (e.l :))
        c := (by with_unfolding_all exact (e.c :))
        Dw := (by with_unfolding_all exact (e.Dw :))
        Xo := (by with_unfolding_all exact (e.Xo :))
        U := (by with_unfolding_all exact (e.U :))
        V := (by with_unfolding_all exact (e.V :))
        dict := (by with_unfolding_all exact (e.dict :))
        mu := (by with_unfolding_all exact (e.mu :))
        Kf := (by with_unfolding_all exact (e.Kf :))
        cE := (by with_unfolding_all exact (e.cE :))
        chiW := (by with_unfolding_all exact (e.chiW :))
        x₀ := (by with_unfolding_all exact (e.x₀ :))
        iota := (by with_unfolding_all exact (e.iota :))
        ψ := (by with_unfolding_all exact (e.ψ :))
        θ := (by with_unfolding_all exact (e.θ :))
        βW := (by with_unfolding_all exact (e.βW :))
        βY := (by with_unfolding_all exact (e.βY :))
        nW := (by with_unfolding_all exact (e.nW :))
        βV := (by with_unfolding_all exact (e.βV :))
        ΛV := (by with_unfolding_all exact (e.ΛV :))
        ΛW := (by with_unfolding_all exact (e.ΛW :))
        Pg := (by with_unfolding_all exact (e.Pg :))
        eG := (by with_unfolding_all exact (e.eG :))
        Sb := (by with_unfolding_all exact (e.Sb :))
        BV := (by with_unfolding_all exact (e.BV :))
        MW := (by with_unfolding_all exact (e.MW :))
        forms := (by with_unfolding_all exact (e.forms :))
        cV := (by with_unfolding_all exact (e.cV :))
        pb := (by with_unfolding_all exact (e.pb :))
        ΛY := (by with_unfolding_all exact (e.ΛY :))
        κ := (by with_unfolding_all exact (e.κ :))
        ref := (by with_unfolding_all exact (e.ref :))
        jL := (by with_unfolding_all exact (e.jL :)) }

end GlobalTheory.HeightCounting.SerMove.ReGeo

namespace GlobalTheory.HeightCounting.SerMove

theorem exists_geo_extN : ∀ {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'}, Ext P.z P'.z → ∀ (x : St P) (x' : St P'), ∃ (g : Geo x) (g' : Geo x'), GlobalTheory.RealGeo.InGeo g ∧ GlobalTheory.RealGeo.InGeo g' ∧ ExtN (datAt x g) (datAt x' g') := by
  intro K B B' f f' T T' w w' P P' e x x'
  obtain ⟨g, hg, hL, -⟩ := ReGeo.geo_copy (Z := P.Z₀) (Z' := x.o.Z) P.z x.m.z x.m.Xg x.m.tr ((by with_unfolding_all exact (x.copy.core :))) ((by with_unfolding_all exact (x.copy.R :))) P.inGeo
  obtain ⟨g', hg', -, hR⟩ :=
    ReGeo.geo_copy (Z := P'.Z₀) (Z' := x'.o.Z) P'.z x'.m.z x'.m.Xg x'.m.tr ((by with_unfolding_all exact (x'.copy.core :))) ((by with_unfolding_all exact (x'.copy.R :))) P'.inGeo
  exact ⟨g, g', hg, hg', hR _ (hL _ e.extN)⟩

end GlobalTheory.HeightCounting.SerMove
end

section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
open GlobalTheory.HeightCounting.SerMove GlobalTheory.HeightCounting.SideCopy GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.HeightCounting.SerGlue

theorem copyAll_ex {D D' : D7} {N : TwNew D'} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0}
    (h : CopyN D N ι e) (hp : HEq D.naut.plGw D'.naut.plGw) {D'' : D7} (hD : D'' = N.toD7) :
    ∃ ι' e', CopyAll D D'' ι' e' := by
  subst hD
  exact ⟨ι, e, h.cp, h.jL, h.s2, h.lamG, h.Xv, h.qs, hp⟩

theorem fr_same {A A' : Pre} (h : A' = A) {f : Top.Fr A} {f' : Top.Fr A'} (hf : HEq f' f) :
    HEq f.mu0 f'.mu0 ∧ HEq f.eta f'.eta ∧ HEq f.del f'.del ∧ HEq f.del' f'.del' := by
  subst h; cases hf; exact ⟨HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩

theorem choice_heq {A A' : Pre} (h : A' = A)
    {p : HeightOneSpectrum (𝓞 (maximalRealSubfield A.host.E)) → HeightOneSpectrum (𝓞 A.host.E)}
    {p' : HeightOneSpectrum (𝓞 (maximalRealSubfield A'.host.E)) → HeightOneSpectrum (𝓞 A'.host.E)}
    (hp : ∀ v, NG.OverPl (p v) v) (hp' : ∀ v, NG.OverPl (p' v) v)
    {s : HeightOneSpectrum (𝓞 A.host.F) → HeightOneSpectrum (𝓞 A.host.E)}
    {s' : HeightOneSpectrum (𝓞 A'.host.F) → HeightOneSpectrum (𝓞 A'.host.E)} (hs : HEq s' s)
    (r : Set.range p = Set.range s) (r' : Set.range p' = Set.range s') : HEq p p' := by
  subst h; cases hs
  refine heq_of_eq (funext fun v => ?_)
  obtain ⟨u, hu⟩ : p v ∈ Set.range p' := by rw [r', ← r]; exact ⟨v, rfl⟩
  have h1 := hp' u
  rw [hu] at h1
  obtain rfl : u = v := HeightOneSpectrum.ext (h1.symm.trans (hp v))
  exact hu.symm

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B}
  {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'}

theorem bigHost_st (hO : K.Over B.toPre)
    (hB : ∀ X : Stages, K.Over X.B.toPre → Formalism.IndefR.Links.HostHyp X.toD7 ∧ 8 * X.toD7.R.f * X.toD7.R.r + 4 ≤ X.toD7.R.nV)
    (x : St P) : BigHost (Dof x) :=
  ⟨(hB (w.st x.o.Z) hO).1, GlobalTheory.HeightCounting.FirstFacts.vstd_of_over (w.st x.o.Z) hO, (hB (w.st x.o.Z) hO).2⟩

theorem exists_move (hKP : KPx B' f') (hF : Forced K B' T') (hS' : Start K B' f' T' w') (hO : K.Over B'.toPre)
    (hB : ∀ X : Stages, K.Over X.B.toPre → Formalism.IndefR.Links.HostHyp X.toD7 ∧ 8 * X.toD7.R.f * X.toD7.R.r + 4 ≤ X.toD7.R.nV)
    (hE : Enl B B') (hf : HEq f' f) (hSt : Start K B f T w) (hpx : HEq w'.px w.px) (hsel : HEq w'.I.sel w.I.sel)
    (hJ : HEq w'.I.J w.I.J) (hδ : HEq w'.δ w.δ) (x : St P) (l : LA hL x) (hExt : Ext P.z P'.z) (x' : St P')
    (hG : SameGal (Dof x) (Dof x')) (N : TwNew (Dof x')) {ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL}
    {e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0} (hN : CopyN (Dof x) N ι e) (x'' : St P') (l'' : LA hL x'') (ho : x''.o = oTw x' N) :
    ∃ (ι' : (Dof x).what₂.LL →+* (Dof x'').what₂.LL) (e' : ↥(Dof x'').LL0 ≃+* ↥(Dof x).LL0), CopyAll (Dof x) (Dof x'') ι' e' ∧
      SameFrame (cfOf x) (cfOf x'') ∧ HEq l.Pq l''.Pq ∧
      ∃ (g : Geo x) (g'' : Geo x'') (hg : GlobalTheory.RealGeo.InGeo g) (hg'' : GlobalTheory.RealGeo.InGeo g'') (a : BigHost (Dof x))
        (a'' : BigHost (Dof x'')), Nonempty (GlobalTheory.TwInputs.Move.RealMove (sideAt x g hg a) (sideAt x'' g'' hg'' a'') ι') := by
  have hD : Dof x'' = N.toD7 := by
    show (w'.st x''.o.Z).toD7 = N.toD7
    rw [ho]; rfl
  obtain ⟨ι', e', h⟩ := copyAll_ex hN hG.pl hD
  obtain ⟨h1, h2, h3, h4⟩ := fr_same hE.1 ((heq_of_eq w'.C_eq).trans (hf.trans (heq_of_eq w.C_eq).symm))
  obtain ⟨g, g'', hg, hg'', hX⟩ := GlobalTheory.HeightCounting.SerMove.exists_geo_extN hExt x x''
  have hO' : K.Over B.toPre := hE.1 ▸ hO
  exact ⟨ι', e', h, ⟨(by with_unfolding_all exact (h1 :)), (by with_unfolding_all exact (h2 :)), (by with_unfolding_all exact (h3 :)), (by with_unfolding_all exact (h4 :))⟩,
    (by with_unfolding_all exact ((choice_heq hE.1 (p := (by with_unfolding_all exact (l.Pq :))) (p' := (by with_unfolding_all exact (l''.Pq :))) ((by with_unfolding_all exact (l.Pq_over :))) ((by with_unfolding_all exact (l''.Pq_over :))) (s := (by with_unfolding_all exact (w.I.sel :))) (s' := (by with_unfolding_all exact (w'.I.sel :))) ((by with_unfolding_all exact (hsel :))) ((by with_unfolding_all exact (l.sel :))) ((by with_unfolding_all exact (l''.sel :)))) :)),
    g, g'', hg, hg'', bigHost_st hO' hB x, bigHost_st hO hB x'',
    GlobalTheory.HeightCounting.SerMove.realMove_of_link x x'' ι' e' g g'' ⟨hO, hKP, hF, hS', hE, hf, hSt, hpx, hsel, hJ, hδ, hExt, h.cp, ⟨h.cp.gal, h.pl⟩, hX⟩ hg hg'' _ _⟩

end GlobalTheory.HeightCounting.SerGlue

end
end
