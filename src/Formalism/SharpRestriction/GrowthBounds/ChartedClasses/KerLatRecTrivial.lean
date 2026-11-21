import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.MovDXiAtRecStep
import Formalism.SharpRestriction.GrowthBounds.ChartComparison.PStabEq
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.InTwSt
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ToLEInvApply
import Formalism.SharpRestriction.GrowthBounds.TensorLatticeBounds.DataForm
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.RepTwLat

section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.MainNotions.G.CmpJ
open Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.UG
open scoped TensorProduct

namespace Formalism.MainNotions.G.KAat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Re

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E}

theorem latK_re {N n : ℕ} (h : N = n) (J : Matrix (Fin N) (Fin N) E) (a : 𝓞 E)
    (y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (Lb : Submodule (𝓞 E) (Fin N → E)) :
    latK sp (J.reindex (finCongr h) (finCongr h)) a (Formalism.L2.PairingIndexBounds.F.reGL (finCongr h) y)
      (Lb.map (((reE (E := E) h : (Fin N → E) ≃ₗ[E] (Fin n → E)) : (Fin N → E) →ₗ[E] (Fin n → E)).restrictScalars (𝓞 E))) =
    (latK sp J a y Lb).map
      (((reE (E := E) h : (Fin N → E) ≃ₗ[E] (Fin n → E)) : (Fin N → E) →ₗ[E] (Fin n → E)).restrictScalars (𝓞 E)) := by
  subst h
  have e1 : J.reindex (finCongr rfl) (finCongr rfl) = J := by
    ext i j
    simp
  have e2 : Formalism.L2.PairingIndexBounds.F.reGL (finCongr (rfl : N = N)) y = y := by
    apply Units.ext
    ext i j
    simp [Formalism.L2.PairingIndexBounds.F.reGL]
  rw [e1, e2, map_reE_rfl, map_reE_rfl]

end Re

section AtS

variable {D : D7} {u : D.what₂.Word} {w : D.what₂.places.Pl} {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
  [Fact (D.what₂.places.resChar w).Prime] {Fl : Fills (D.gat u w h)} {Lv : Levels Fl} (Ch : Chain Lv)
  (std : ∀ v, Std (D.what₂.places.resChar w) ((D.gat u w h).P.n' v) (D.gat u w h).P.m Fl.t Fl.mm Fl.c (D.gat u w h).P.r
    (Fl.TT v) (Fl.a v) (Fl.b v) ((D.gat u w h).P.lam0 v) (Fl.w v))
  (vp : (D.gat u w h).O) (unif : Irreducible vp) (eO : ℕ)
  (eO_spec : Associated ((D.what₂.places.resChar w : ℕ) : (D.gat u w h).O) (vp ^ eO)) (dG : ℕ → ℕ)
  (dG_spec : ∀ j ≤ Fl.mm, ∀ (c : Lv.comp j) (L : (Fl.Pj j).Tup), (Fl.Pj j).IsLatTup L →
    padicValNat (D.what₂.places.resChar w) (Nat.card {γ : (Lv.lev j c).Γ // (Lv.lev j c).smul γ L = L}) ≤ dG j)
  (om : ∀ v, OmBasis (D.what₂.places.resChar w) ((D.gat u w h).P.n' v))
  {μ : D.what₂.Tup} {Tw : TwForms D} (I : CmpJIn Tw u μ w h Lv)
  (L0 : Lev0Data D u w h) (a : 𝓞 D.host.E) (bad : Finset (HeightOneSpectrum (𝓞 D.host.F)))

def ptAt (i : ℕ) (hi : i + 1 ≤ D.R.m) (La : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt (i + 1)) :
    GL (Fin (D.R.N (i + 1))) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F) :=
  Classical.epsilon fun x => ((I.at' i hi).st.loc ((I.at' i hi).st.eC.symm La.1).1).IsPt ((I.at' i hi).st.eC.symm La.1).2
      (basesAt Ch std vp unif eO eO_spec dG dG_spec om (i + 1) La.2) x ∧
    x ∈ Formalism.UG.UPts (sigD D) (gramN D (i + 1) hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)

set_option maxHeartbeats 1600000 in

theorem kerN_succ (i : ℕ) (hi : i + 1 ≤ D.R.m) (La : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt (i + 1)) :
    ((fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad).kerN (i + 1) La).map
      ((reE (E := D.host.E) (rankAt Ch std vp unif eO eO_spec dG dG_spec om I L0 (i + 1) hi La)).toLinearMap.restrictScalars (𝓞 D.host.E)) =
    latK D.sp (gramN D (i + 1) hi) a (ptAt Ch std vp unif eO eO_spec dG dG_spec om I i hi La)
      ((I.at' i hi).st.K ((I.at' i hi).st.eC.symm La.1).1).lev.Lb := by
  have e := latK_re (sp := D.sp) ((I.at' i hi).st.loc ((I.at' i hi).st.eC.symm La.1).1).rk.symm (gramN D (i + 1) hi) a
    (ptAt Ch std vp unif eO eO_spec dG dG_spec om I i hi La) ((I.at' i hi).st.K ((I.at' i hi).st.eC.symm La.1).1).lev.Lb
  have e0 : (fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad).kerN (i + 1) La =
      (latK D.sp (gramN D (i + 1) hi) a (ptAt Ch std vp unif eO eO_spec dG dG_spec om I i hi La)
        ((I.at' i hi).st.K ((I.at' i hi).st.eC.symm La.1).1).lev.Lb).map
      ((reE (E := D.host.E) ((I.at' i hi).st.loc ((I.at' i hi).st.eC.symm La.1).1).rk.symm).toLinearMap.restrictScalars (𝓞 D.host.E)) := by
    rw [← e]
    simp only [fdAtL, fdAt, fdOfCharts, cpAt, chAt, dif_pos hi]
    exact map_reE_rfl _ _
  rw [e0]
  exact map_reE_symm _ _ _

end AtS

section Spec

variable {D : D7} {u : D.what₂.Word} {w : D.what₂.places.Pl} {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
  [Fact (D.what₂.places.resChar w).Prime] {Fl : Fills (D.gat u w h)} {Lv : Levels Fl} (Ch : Chain Lv)
  (std : ∀ v, Std (D.what₂.places.resChar w) ((D.gat u w h).P.n' v) (D.gat u w h).P.m Fl.t Fl.mm Fl.c (D.gat u w h).P.r
    (Fl.TT v) (Fl.a v) (Fl.b v) ((D.gat u w h).P.lam0 v) (Fl.w v))
  (vp : (D.gat u w h).O) (unif : Irreducible vp) (eO : ℕ)
  (eO_spec : Associated ((D.what₂.places.resChar w : ℕ) : (D.gat u w h).O) (vp ^ eO)) (dG : ℕ → ℕ)
  (dG_spec : ∀ j ≤ Fl.mm, ∀ (c : Lv.comp j) (L : (Fl.Pj j).Tup), (Fl.Pj j).IsLatTup L →
    padicValNat (D.what₂.places.resChar w) (Nat.card {γ : (Lv.lev j c).Γ // (Lv.lev j c).smul γ L = L}) ≤ dG j)
  (om : ∀ v, OmBasis (D.what₂.places.resChar w) ((D.gat u w h).P.n' v))
  {μ : D.what₂.Tup} {Tw : TwForms D}

set_option maxHeartbeats 1600000 in

theorem basesAt_spec (i : ℕ) (Lt : ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj (i + 1)).Tup) (hL : ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj (i + 1)).IsLatTup Lt) (v : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pl) :
    (sysAt Ch std vp unif eO eO_spec dG dG_spec om).latAt v (i + 1) Lt = colSpan ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).G.P.W v) (basesAt Ch std vp unif eO eO_spec dG dG_spec om (i + 1) Lt v : Matrix _ _ _) := by
  obtain ⟨g, hg⟩ := (isLattice_iff _ ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).latAt v (i + 1) Lt)).1 (hL v)
  exact Classical.epsilon_spec (p := fun g : GL (Fin (((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj (i + 1)).m + 1)) ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).G.P.Qq v) => (sysAt Ch std vp unif eO eO_spec dG dG_spec om).latAt v (i + 1) Lt =
    colSpan ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).G.P.W v) (g : Matrix _ _ _)) ⟨g, by rw [hg, colSpan_eq]⟩


end Spec

end Formalism.MainNotions.G.KAat

end
end

section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.MainNotions.G.CmpJ
open Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.UG
open scoped TensorProduct

namespace Formalism.MainNotions.G.KAat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section SlopeTestRemainingChoices

variable {p : ℕ} [Fact p.Prime] {X : Sys p} {D : D7}

theorem latAt_eq_of_kerN (fd : FData X D) (j : ℕ) (La Lb : X.Lt j) (v : X.Pl) (ρ : D.host.E →+* X.G.P.Qq v)
    (hk : fd.kerN j La = fd.kerN j Lb) (hf : fd.frM j La v = fd.frM j Lb v)
    (hWa : Formalism.L2.KerInert.RepTwLat.locSpan D (X.G.P.W v) ρ (fd.kerN j La) =
      (X.latAt v j La.2).map (((fd.frM j La v).mulVecLin).restrictScalars (X.G.P.W v)))
    (hWb : Formalism.L2.KerInert.RepTwLat.locSpan D (X.G.P.W v) ρ (fd.kerN j Lb) =
      (X.latAt v j Lb.2).map (((fd.frM j Lb v).mulVecLin).restrictScalars (X.G.P.W v)))
    (hM : Function.Injective (fd.frM j Lb v).mulVecLin) : X.latAt v j La.2 = X.latAt v j Lb.2 := by
  rw [hk, hWb, hf] at hWa
  exact (Submodule.map_injective_of_injective (f := ((fd.frM j Lb v).mulVecLin).restrictScalars (X.G.P.W v)) hM hWa).symm

end SlopeTestRemainingChoices

section Rec

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc0 : G.Consts} {Dx : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc0 Dx cX} {u : D.what₂.Word} {w : D.what₂.places.Pl}
  {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
  [Fact (D.what₂.places.resChar w).Prime] {Fl : Fills (D.gat u w h)} {Lv : Levels Fl} (Ch : Chain Lv)
  (std : ∀ v, Std (D.what₂.places.resChar w) ((D.gat u w h).P.n' v) (D.gat u w h).P.m Fl.t Fl.mm Fl.c (D.gat u w h).P.r
    (Fl.TT v) (Fl.a v) (Fl.b v) ((D.gat u w h).P.lam0 v) (Fl.w v))
  (vp : (D.gat u w h).O) (unif : Irreducible vp) (eO : ℕ)
  (eO_spec : Associated ((D.what₂.places.resChar w : ℕ) : (D.gat u w h).O) (vp ^ eO)) (dG : ℕ → ℕ)
  (dG_spec : ∀ j ≤ Fl.mm, ∀ (c : Lv.comp j) (L : (Fl.Pj j).Tup), (Fl.Pj j).IsLatTup L →
    padicValNat (D.what₂.places.resChar w) (Nat.card {γ : (Lv.lev j c).Γ // (Lv.lev j c).smul γ L = L}) ≤ dG j)
  (om : ∀ v, OmBasis (D.what₂.places.resChar w) ((D.gat u w h).P.n' v))
  {μ : D.what₂.Tup} (I : CmpJIn ex.tw u μ w h Lv)
  (L0 : Lev0Data D u w h) (a : 𝓞 D.host.E) (bad : Finset (HeightOneSpectrum (𝓞 D.host.F)))
  (t : KerEntTied ex) (cls : ∀ j, Lv.comp j → (Fl.Pj j).Tup → (D.chTw u μ).cls j)

def KerLatRec : Prop :=
  ∀ j (hj : j ≤ D.R.m) (La : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt j),
    t.seam.lat ((t.rd u μ).N j (cls j La.1 La.2)) =
      ((fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad).kerN j La).map
        ((reE (E := D.host.E) (rankAt Ch std vp unif eO eO_spec dG dG_spec om I L0 j hj La)).toLinearMap.restrictScalars (𝓞 D.host.E))

variable {Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad t cls}

theorem kerLatRec_const (H : KerLatRec Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad t cls) (j : ℕ) (hj : j ≤ D.R.m)
    (La Lb : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt j) (hc : cls j La.1 La.2 = cls j Lb.1 Lb.2) :
    (fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad).kerN j La = (fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad).kerN j Lb := by
  have h1 := H j hj La
  have h2 := H j hj Lb
  rw [hc, h2] at h1
  exact (Submodule.map_injective_of_injective (f := (reE (E := D.host.E)
    (rankAt Ch std vp unif eO eO_spec dG dG_spec om I L0 j hj La)).toLinearMap.restrictScalars (𝓞 D.host.E))
    (reE (E := D.host.E) (rankAt Ch std vp unif eO eO_spec dG dG_spec om I L0 j hj La)).injective h1).symm

theorem kerLatRec_orbit (KA : TwTie.KerAtMu D ex.cmp ex.tw u μ w h Ch)
    (H : KerLatRec Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad t KA.cls) (j : ℕ) (hj : j ≤ D.R.m)
    (c : Lv.comp j) (Lt : (Fl.Pj j).Tup) (hL : (Fl.Pj j).IsLatTup Lt) (γ : (Lv.lev j c).Γ) :
    (fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad).kerN j (c, (Lv.lev j c).smul γ Lt) =
      (fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad).kerN j (c, Lt) :=
  kerLatRec_const H j hj (c, (Lv.lev j c).smul γ Lt) (c, Lt)
    ((KA.cls_iff j hj c c Lt _ hL ((Formalism.MainNotions.G.Inhab.isLatTup_smul_iff _ _ γ Lt).2 hL)).2 ⟨rfl, γ, rfl⟩).symm

set_option maxHeartbeats 1600000 in

theorem frM_comp (i : ℕ) (c : Lv.comp (i + 1)) (Lt Lt' : (Fl.Pj (i + 1)).Tup) (v : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pl) :
    (fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad).frM (i + 1) (c, Lt) v = (fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad).frM (i + 1) (c, Lt') v := by
  by_cases hi : i + 1 ≤ D.R.m
  · simp only [fdAtL, fdAt, fdOfCharts, cpAt, chAt, dif_pos hi]
    rfl
  · simp only [fdAtL, fdAt, fdOfCharts, cpAt, chAt, dif_neg hi]
    rfl

set_option maxHeartbeats 3200000 in

theorem kerLatRec_trivial (KA : TwTie.KerAtMu D ex.cmp ex.tw u μ w h Ch)
    (H : KerLatRec Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad t KA.cls) (i : ℕ) (hi : i + 1 ≤ D.R.m)
    (ρ : ∀ v : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pl, D.host.E →+* (sysAt Ch std vp unif eO eO_spec dG dG_spec om).G.P.Qq v)
    (hW : ∀ La' : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt (i + 1), ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pj (i + 1)).IsLatTup La'.2 → ∀ v : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pl,
      Formalism.L2.KerInert.RepTwLat.locSpan D ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).G.P.W v) (ρ v) ((fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad).kerN (i + 1) La') =
        ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).latAt v (i + 1) La'.2).map
          ((((fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad).frM (i + 1) La' v).mulVecLin).restrictScalars ((sysAt Ch std vp unif eO eO_spec dG dG_spec om).G.P.W v)))
    (hM : ∀ (La' : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Lt (i + 1)) (v : (sysAt Ch std vp unif eO eO_spec dG dG_spec om).Pl),
      Function.Injective ((fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad).frM (i + 1) La' v).mulVecLin)
    (c : Lv.comp (i + 1)) (Lt : (Fl.Pj (i + 1)).Tup) (hL : (Fl.Pj (i + 1)).IsLatTup Lt) (γ : (Lv.lev (i + 1) c).Γ) :
    (Lv.lev (i + 1) c).smul γ Lt = Lt := by
  funext v
  exact latAt_eq_of_kerN (fdAtL Ch std vp unif eO eO_spec dG dG_spec om I L0 a bad) (i + 1) (c, (Lv.lev (i + 1) c).smul γ Lt) (c, Lt) v (ρ v)
    (kerLatRec_orbit KA H (i + 1) hi c Lt hL γ) (frM_comp i c _ Lt v)
    (hW (c, (Lv.lev (i + 1) c).smul γ Lt) ((Formalism.MainNotions.G.Inhab.isLatTup_smul_iff _ _ γ Lt).2 hL) v) (hW (c, Lt) hL v) (hM (c, Lt) v)

end Rec

end Formalism.MainNotions.G.KAat

end
end
