import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypesTrueOfRayClassStatement
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayPrimeHostIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowDepthOfPrimitive
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyAllIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FcLargeOfSup
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WeakCharInertPartRealAdelicDataTransport
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMovedRowLiftDataToFittingStages
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicRowsReadingTransportLaterHeckeGaloisStage

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.HeightCounting

theorem omFrame_exists_with_jE (D : D7) (jE : D.host.E →+* Qb) : ∃ fr : OmFrame D, fr.jE = jE := by
  letI : Algebra D.host.E Qb := jE.toAlgebra
  haveI : Algebra.IsAlgebraic ℚ Qb := inferInstance
  haveI : IsScalarTower ℚ D.host.E Qb := .of_algebraMap_eq fun x => (map_ratCast jE x).symm
  haveI : Algebra.IsAlgebraic D.host.E Qb := .tower_top (K := ℚ) D.host.E
  haveI : IsAlgClosure D.host.E Qb := ⟨inferInstance, inferInstance⟩
  let e : D.nd.Om ≃ₐ[D.host.E] Qb := IsAlgClosure.equiv D.host.E D.nd.Om Qb
  exact ⟨⟨jE, e.toRingEquiv, fun x => e.commutes x⟩, rfl⟩

end GlobalTheory.HeightCounting
end
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.HeightCounting.PhtExt

variable {D : D7} {T : GlobalTheory.RowTie.WDTie D.nd D.naut}

theorem continuous_mapRep {Γ : Type} [Group Γ] [TopologicalSpace Γ] {A B : Type} [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B] {a : ℕ} (f : A →+* B) (hf : Continuous f) (ρ : Γ →* GL (Fin a) A)
    (hρ : Continuous fun g => ((ρ g : GL (Fin a) A) : Matrix (Fin a) (Fin a) A)) :
    Continuous fun g => ((mapRep f ρ g : GL (Fin a) B) : Matrix (Fin a) (Fin a) B) := by
  have : (fun g => ((mapRep f ρ g : GL (Fin a) B) : Matrix (Fin a) (Fin a) B)) =
      fun g => ((ρ g : GL (Fin a) A) : Matrix (Fin a) (Fin a) A).map f := by
    funext g; rfl
  rw [this]
  exact hρ.matrix_map hf

end GlobalTheory.HeightCounting.PhtExt

namespace GlobalTheory.HeightCounting.PhtExt

variable {D : D7} {T : GlobalTheory.RowTie.WDTie D.nd D.naut}

noncomputable def ext (Wd₀ : WDSide D T) : WDSide D T :=
  { Wd₀ with
    IsdRW := fun l _ ι a r w =>
      (Continuous fun g => ((r g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) ∧ Wd₀.IsdRW l ι r w
    wdOf_unrL := fun l _ ι _ r w hw hc hd => Wd₀.wdOf_unrL l ι r w hw hc hd.2
    wdOf_mono0L := fun l _ ι _ r w hw hc hd => Wd₀.wdOf_mono0L l ι r w hw hc hd.2
    loc := by
      intro l _ ι w hw O _ _ _ Bw hB φ hφ
      obtain ⟨h1, h2⟩ := Wd₀.loc l ι w hw O Bw hB φ hφ
      have hφc : Continuous φ := by
        have e : (φ : O → Qbar l) = fun x => ((Bw.toLL x : ↥Bw.LL.1) : Loc.Om l) := funext hφ
        rw [e]
        unfold LocBridge.toLL
        exact continuous_subtype_val.comp (continuous_subtype_val.comp Bw.eO_cont)
      refine ⟨fun m ρ hρ => ?_, fun LL' hLL' m ρ hρ => ?_⟩
      · obtain ⟨c1, c2, c3, c4⟩ := h1 m ρ hρ
        exact ⟨c1, (and_iff_right (continuous_mapRep φ hφc ρ hρ)).trans c2, c3, c4⟩
      · have hf : Continuous (algebraMap ↥LL'.1 (Qbar l)) := continuous_subtype_val
        obtain ⟨c1, c2, c3, c4⟩ := h2 LL' hLL' m ρ hρ
        exact ⟨c1, (and_iff_right (continuous_mapRep _ hf ρ hρ)).trans c2, c3, c4⟩ }

theorem exists_phtOn_all : PhtCmp → ∀ (D : D7) (fr : OmFrame D) (T : GlobalTheory.RowTie.WDTie D.nd D.naut), WDSide D T →
    ∃ Wd : WDSide D T, PhtOn Wd fr fun _ _ _ _ => True := by
  intro hP D fr T Wd₀
  exact ⟨ext Wd₀, ⟨fun l _ ι a r τ w _ hw hd => (hP D fr T Wd₀).card l ι a r τ w hd.1 hw hd.2⟩⟩

end GlobalTheory.HeightCounting.PhtExt
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open GlobalTheory.Mem.Top.TypesTrue GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.Rw.CopySide

theorem mem_center_map {G G' : Type} [Monoid G] [Monoid G'] (φ : MonoidAlgebra ℂ G ≃ₐ[ℂ] MonoidAlgebra ℂ G')
    {a : MonoidAlgebra ℂ G} (ha : a ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ G)) :
    φ a ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ G') := by
  rw [Subalgebra.mem_center_iff] at ha ⊢
  intro b
  obtain ⟨b, rfl⟩ := φ.surjective b
  rw [← map_mul, ← map_mul, ha b]

def cenMap {G H : Type} [Group G] [Group H] (e : G ≃* H) :
    Subalgebra.center ℂ (MonoidAlgebra ℂ G) →ₐ[ℂ] Subalgebra.center ℂ (MonoidAlgebra ℂ H) :=
  ((MonoidAlgebra.domCongr ℂ ℂ e).toAlgHom.comp (Subalgebra.center ℂ (MonoidAlgebra ℂ G)).val).codRestrict _ fun z =>
    mem_center_map (MonoidAlgebra.domCongr ℂ ℂ e) z.2

theorem cenMap_coeff {G H : Type} [Group G] [Group H] (e : G ≃* H) (z : Subalgebra.center ℂ (MonoidAlgebra ℂ G)) (h : H) :
    ((cenMap e z : Subalgebra.center ℂ (MonoidAlgebra ℂ H)) : MonoidAlgebra ℂ H).coeff h =
      (z : MonoidAlgebra ℂ G).coeff (e.symm h) := by
  show (MonoidAlgebra.domCongr ℂ ℂ e (z : MonoidAlgebra ℂ G)).coeff h = _
  rw [MonoidAlgebra.coeff_domCongr]

theorem domCongr_symm_eq {G H : Type} [Group G] [Group H] (e : G ≃* H) (a : MonoidAlgebra ℂ H) (b : MonoidAlgebra ℂ G)
    (h : ∀ g, a.coeff (e g) = b.coeff g) : MonoidAlgebra.domCongr ℂ ℂ e.symm a = b := by
  apply MonoidAlgebra.coeff_injective
  refine Finsupp.ext fun g => ?_
  rw [MonoidAlgebra.coeff_domCongr, MulEquiv.symm_symm]
  exact h g

theorem domCongr_eq {G H : Type} [Group G] [Group H] (e : G ≃* H) (a : MonoidAlgebra ℂ H) (b : MonoidAlgebra ℂ G)
    (h : ∀ g, a.coeff (e g) = b.coeff g) : MonoidAlgebra.domCongr ℂ ℂ e b = a := by
  apply MonoidAlgebra.coeff_injective
  refine Finsupp.ext fun g => ?_
  rw [MonoidAlgebra.coeff_domCongr, ← h, MulEquiv.apply_symm_apply]

open Classical in

theorem tie_tr {G H E : Type} [Group G] [Group H] [AddCommGroup E] [Module ℂ E] (e : G ≃* H)
    (cen : Subalgebra.center ℂ (MonoidAlgebra ℂ G) →ₐ[ℂ] Module.End ℂ E) (a : MonoidAlgebra ℂ G) (b : MonoidAlgebra ℂ H)
    (h : ∀ g, b.coeff (e g) = a.coeff g) :
    (if ha : a ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ G) then cen ⟨a, ha⟩ else 0) =
      (if hb : b ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ H) then (cen.comp (cenMap e.symm)) ⟨b, hb⟩ else 0) := by
  have h1 := domCongr_symm_eq e b a h
  have h2 := domCongr_eq e b a h
  by_cases hb : b ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ H)
  · have ha : a ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ G) := by
      rw [← h1]; exact mem_center_map _ hb
    rw [dif_pos ha, dif_pos hb, AlgHom.comp_apply]
    congr 1
    exact Subtype.ext h1.symm
  · have ha : a ∉ Subalgebra.center ℂ (MonoidAlgebra ℂ G) := by
      intro ha; apply hb; rw [← h2]; exact mem_center_map _ ha
    rw [dif_neg ha, dif_neg hb]

set_option maxHeartbeats 1000000 in

theorem side_copy : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (N : NStage B w.C (P.q.W x.o.η x.o.hη)), GrpTrue N f → ∃ (sg : SameGrp (B := B) (C := w.C) x.o.Z (RowPk.Over.Z (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over))) (s : Side0 (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over)), s.RR = x.s.RR ∧ HEq s.jEE x.s.jEE ∧ ∀ μ (c : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g (w.D (RowPk.Over.Z (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over))).nd))) (c0 : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g (w.D x.o.Z).nd))), (∀ g, (c0 : MonoidAlgebra ℂ (G0g (w.D x.o.Z).nd)).coeff g = (c : MonoidAlgebra ℂ (G0g (w.D (RowPk.Over.Z (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over))).nd)).coeff (sg.iso g)) → s.cen μ c = x.s.cen μ c0 := by
  intro K B f T w P x N hN
  let sg : SameGrp (B := B) (C := w.C) x.o.Z (RowPk.Over.Z (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over)) :=
    { e := (by with_unfolding_all exact ((plEquiv x.o.N.naut N.naut) :))
      pl := (by with_unfolding_all exact ((TypesTrue.plGw_plEquiv x.fits.grp hN) :))
      e0 := (by with_unfolding_all exact ((x.fits.grp.typeIdempotent_coeff_across_layers hN) :)) }
  let φ := cenMap sg.iso.symm
  have hφ : ∀ c g, (φ c).val.coeff g = c.val.coeff (sg.iso g) := by
    intro c g
    rw [cenMap_coeff, MulEquiv.symm_symm]

  have hstd : ∀ eR, StdIso (w.st (RowPk.Over.Z (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over))) w.px eR →
      StdIso (w.st x.o.Z) w.px (eR.trans sg.iso.symm) := by
    rintro eR ⟨plg1, iso1, hpl1, hact1⟩
    refine ⟨(Equiv.sigmaCongrRight fun k => sg.e k).trans plg1, fun kv => iso1 ⟨kv.1, sg.e kv.1 kv.2⟩, fun kv => ?_, fun g kv => ?_⟩
    · exact (hpl1 _).trans (sg.pl kv.1 kv.2)
    · exact hact1 g _
  refine ⟨sg, { cen := fun μ => (x.s.cen μ).comp φ
                tie := fun μ => (x.s.tie μ).trans ((by with_unfolding_all exact ((tie_tr sg.iso (x.s.cen μ) _ _ sg.e0) :)))
                is := fun eR h μ c c' hc xx => ?_
                RR := x.s.RR
                frames := x.s.frames
                jEE := x.s.jEE
                basis := x.s.basis
                norm := x.s.norm }, rfl, HEq.rfl, fun μ c c0 hc => ?_⟩
  · show x.s.cen μ (φ c) xx = _
    refine x.s.is (eR.trans sg.iso.symm) (hstd eR h) μ (φ c) c' (fun g => ?_) xx
    exact (hc g).trans ((congrArg c.val.coeff (sg.iso.apply_symm_apply (eR g))).symm.trans (hφ c _).symm)
  · show x.s.cen μ (φ c) = _
    congr 1
    apply Subtype.ext
    apply MonoidAlgebra.coeff_injective
    refine Finsupp.ext fun g => ?_
    exact (hφ c g).trans (hc g).symm

end GlobalTheory.Mem.R3.Rw.CopySide

end
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.R3.Rw

theorem exists_st_copyN : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (N : NStage B w.C (P.q.W x.o.η x.o.hη)), GrpTrue N f → GrpAt (w.st (RowPk.Over.Z (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over))) w.I → (∀ eR, StdIso (w.st (RowPk.Over.Z (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over))) w.px eR → CenIs P.q.p N eR) → ∃ x' : St P, x'.o = ⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ ∧ HEq (repOf x'.r.Y) (repOf x.r.Y) := by
  intro K B f T w P x N hG hGA hCen
  have fits' : RowPk.Over.Fits (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over) := ⟨x.fits.div, hG, hGA, hCen⟩
  obtain ⟨m, hc, hco⟩ := Mv.exists_moved B f T w P.Z₀ P.hX P.Wt P.z P.q _ P.intersectionNumber_baseChange P.exAt P.inGeo P.grp fits'
  obtain ⟨sg, s, h1, h2, h3⟩ := CopySide.side_copy x N hG
  obtain ⟨r, hpin, hrep⟩ := GlobalTheory.T.adelicRowsReading_transport_laterHeckeGaloisStage x N hG hGA hCen m hc hco sg s h1 h2 h3
  exact ⟨⟨_, fits', x.G_eq, x.etaF, x.bk, m, hc, hco, s, r, hpin⟩, rfl, hrep⟩

end GlobalTheory.Mem.R3.Rw
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_transported_state_heckeGaloisStage : (∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (N : NStage B w.C (P.q.W x.o.η x.o.hη)), GrpTrue N f → GrpAt (w.st (RowPk.Over.Z (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over))) w.I → (∀ eR, StdIso (w.st (RowPk.Over.Z (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over))) w.px eR → CenIs P.q.p N eR) → ∃ x' : St P, x'.o = ⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ ∧ HEq (repOf x'.r.Y) (repOf x.r.Y)) := by
  atlas_forward_decl GlobalTheory.Mem.R3.Rw.exists_st_copyN
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.SwapN

open GlobalTheory.Mem.Top.TypesTrue

theorem heq_apply_cast {X : Type*} {P P' : Fin 2 → Type} (h : P = P') {a : ∀ k, P k → X} {a' : ∀ k, P' k → X}
    (ha : HEq a a') (k : Fin 2) (v : P k) : a' k (cast (congrFun h k) v) = a k v := by
  subst h
  obtain rfl := eq_of_heq ha
  rfl

theorem cen_transport {r : ℕ} {g : Fin 2 → ℕ} {P P' : Fin 2 → Type} (h : P = P') {ι : Type*} {E : ι → Type*}
    [∀ i, AddCommGroup (E i)] [∀ i, Module ℂ (E i)]
    {c : ∀ i, Subalgebra.center ℂ (MonoidAlgebra ℂ (∀ kv : (Σ k : Fin 2, P k), GL (Fin r) (ZMod (g kv.1)))) →ₐ[ℂ]
      Module.End ℂ (E i)}
    {c' : ∀ i, Subalgebra.center ℂ (MonoidAlgebra ℂ (∀ kv : (Σ k : Fin 2, P' k), GL (Fin r) (ZMod (g kv.1)))) →ₐ[ℂ]
      Module.End ℂ (E i)}
    (hc : HEq c c')
    (e : (∀ kv : (Σ k : Fin 2, P k), GL (Fin r) (ZMod (g kv.1))) ≃* (∀ kv : (Σ k : Fin 2, P' k), GL (Fin r) (ZMod (g kv.1))))
    (he : ∀ x k v, e x ⟨k, cast (congrFun h k) v⟩ = x ⟨k, v⟩) (i : ι) (z : Subalgebra.center ℂ (MonoidAlgebra ℂ (∀ kv : (Σ k : Fin 2, P k), GL (Fin r) (ZMod (g kv.1)))))
    (z₁ : Subalgebra.center ℂ (MonoidAlgebra ℂ (∀ kv : (Σ k : Fin 2, P' k), GL (Fin r) (ZMod (g kv.1))))) (hz : ∀ x, (z₁ : MonoidAlgebra ℂ _).coeff (e x) =
      (z : MonoidAlgebra ℂ _).coeff x) : c i z = c' i z₁ := by
  subst h
  obtain rfl := eq_of_heq hc
  have he' : ∀ x, e x = x := fun x => funext fun kv => he x kv.1 kv.2
  congr 1
  apply Subtype.ext
  apply MonoidAlgebra.coeff_injective
  refine Finsupp.ext fun x => ?_
  have := hz x
  rw [he'] at this
  exact this.symm

theorem cen_transport₂ {r : ℕ} {g : Fin 2 → ℕ} {P P' : Fin 2 → Type} (h : P = P') {ι κ : Type*} {E : ι → κ → Type*}
    [∀ i j, AddCommGroup (E i j)] [∀ i j, Module ℂ (E i j)]
    {c : ∀ i j, Subalgebra.center ℂ (MonoidAlgebra ℂ (∀ kv : (Σ k : Fin 2, P k), GL (Fin r) (ZMod (g kv.1)))) →ₐ[ℂ]
      Module.End ℂ (E i j)}
    {c' : ∀ i j, Subalgebra.center ℂ (MonoidAlgebra ℂ (∀ kv : (Σ k : Fin 2, P' k), GL (Fin r) (ZMod (g kv.1)))) →ₐ[ℂ]
      Module.End ℂ (E i j)}
    (hc : HEq c c')
    (e : (∀ kv : (Σ k : Fin 2, P k), GL (Fin r) (ZMod (g kv.1))) ≃* (∀ kv : (Σ k : Fin 2, P' k), GL (Fin r) (ZMod (g kv.1))))
    (he : ∀ x k v, e x ⟨k, cast (congrFun h k) v⟩ = x ⟨k, v⟩) (i : ι) (j : κ) (z : Subalgebra.center ℂ (MonoidAlgebra ℂ (∀ kv : (Σ k : Fin 2, P k), GL (Fin r) (ZMod (g kv.1)))))
    (z₁ : Subalgebra.center ℂ (MonoidAlgebra ℂ (∀ kv : (Σ k : Fin 2, P' k), GL (Fin r) (ZMod (g kv.1))))) (hz : ∀ x, (z₁ : MonoidAlgebra ℂ _).coeff (e x) =
      (z : MonoidAlgebra ℂ _).coeff x) : c i j z = c' i j z₁ := by
  subst h
  obtain rfl := eq_of_heq hc
  have he' : ∀ x, e x = x := fun x => funext fun kv => he x kv.1 kv.2
  congr 1
  apply Subtype.ext
  apply MonoidAlgebra.coeff_injective
  refine Finsupp.ext fun x => ?_
  have := hz x
  rw [he'] at this
  exact this.symm

theorem mem_center_map {G G' : Type*} [Monoid G] [Monoid G'] (φ : MonoidAlgebra ℂ G ≃ₐ[ℂ] MonoidAlgebra ℂ G')
    {a : MonoidAlgebra ℂ G} (ha : a ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ G)) : φ a ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ G') := by
  rw [Subalgebra.mem_center_iff] at ha ⊢
  intro b
  obtain ⟨b, rfl⟩ := φ.surjective b
  rw [← map_mul, ← map_mul, ha b]

end GlobalTheory.Mem.R3.Rw.SwapN

namespace GlobalTheory.Mem.R3.Rw.SwapN

theorem fits_swap : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (N : NStage B w.C (P.q.W x.o.η x.o.hη)), GrpTrue N f → N.nd.PlG = x.o.N.nd.PlG → HEq N.naut.plGw x.o.N.naut.plGw → HEq N.ntypes.cenAmb x.o.N.ntypes.cenAmb → HEq N.ntypes.cenMt x.o.N.ntypes.cenMt → GrpAt (w.st (RowPk.Over.Z (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over))) w.I ∧ ∀ eR, StdIso (w.st (RowPk.Over.Z (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over))) w.px eR → CenIs P.q.p N eR := by
  intro K B f T w P x N hG hP hw hA hM
  have hG' : GrpTrue x.o.N f := x.fits.grp
  obtain ⟨⟨plg, hplg⟩, hidem, hcen⟩ := x.fits.grpAt
  let e := grpEquiv N.naut x.o.N.naut
  have hco : ∀ g, x.o.N.ntypes.e0.coeff (e g) = N.ntypes.e0.coeff g := GrpTrue.typeIdempotent_coeff_across_layers hG hG'
  let φ := MonoidAlgebra.domCongr ℂ ℂ e
  have hφ : ∀ (a : MonoidAlgebra ℂ (G0g N.nd)) g, (φ a).coeff (e g) = a.coeff g := by
    intro a g
    simp [φ]
  have he0 : N.ntypes.e0 = φ.symm x.o.N.ntypes.e0 := by
    apply MonoidAlgebra.coeff_injective
    refine Finsupp.ext fun g => ?_
    show _ = (MonoidAlgebra.domCongr ℂ ℂ e.symm x.o.N.ntypes.e0).coeff g
    rw [MonoidAlgebra.coeff_domCongr, MulEquiv.symm_symm, hco]
  have hpe : ∀ k v, plEquiv N.naut x.o.N.naut k v = cast (congrFun hP k) v := by
    intro k v
    show (plF x.o.N.naut k).symm (plF N.naut k v) = _
    rw [Equiv.symm_apply_eq]
    apply Subtype.ext
    rw [plF_apply, plF_apply, heq_apply_cast hP hw k v]
  have he : ∀ (g : G0g N.nd) k v, e g ⟨k, cast (congrFun hP k) v⟩ = g ⟨k, v⟩ := by
    intro g k v
    rw [grpEquiv_apply, ← hpe, Equiv.symm_apply_apply]
  refine ⟨⟨⟨(Equiv.sigmaCongrRight fun k => plEquiv N.naut x.o.N.naut k).trans plg, fun kv => ?_⟩, ?_, ?_⟩, ?_⟩
  · obtain ⟨h1, h2⟩ := hplg ⟨kv.1, plEquiv N.naut x.o.N.naut kv.1 kv.2⟩
    refine ⟨?_, h2⟩
    exact h1.trans (TypesTrue.plGw_plEquiv hG hG' kv.1 kv.2)
  · show IsIdempotentElem N.ntypes.e0
    rw [he0]
    exact hidem.map φ.symm
  · show N.ntypes.e0 ∈ _
    rw [he0]
    exact mem_center_map φ.symm hcen
  · rintro eR ⟨plg1, iso1, hpl1, hact1⟩
    have hstd : StdIso (w.st x.o.Z) w.px (eR.trans e) := by
      refine ⟨(Equiv.sigmaCongrRight fun k => (plEquiv N.naut x.o.N.naut k).symm).trans plg1,
        fun kv => iso1 ⟨kv.1, (plEquiv N.naut x.o.N.naut kv.1).symm kv.2⟩, fun kv => ?_, fun g kv => ?_⟩
      · refine (hpl1 ⟨kv.1, (plEquiv N.naut x.o.N.naut kv.1).symm kv.2⟩).trans ?_
        have := TypesTrue.plGw_plEquiv hG hG' kv.1 ((plEquiv N.naut x.o.N.naut kv.1).symm kv.2)
        exact ((congrArg (x.o.N.naut.plGw kv.1) (Equiv.apply_symm_apply (plEquiv N.naut x.o.N.naut kv.1) kv.2)).symm.trans
          this).symm
      · exact hact1 g _
    have hc := x.fits.cen _ hstd
    have hz1 : ∀ (z : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g N.nd))), φ (z : MonoidAlgebra ℂ (G0g N.nd)) ∈
        Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g x.o.N.nd)) := fun z => mem_center_map φ z.2
    refine ⟨fun μ z z' hz xx => ?_, fun μ j z z' hz xx => ?_⟩
    · have h1 := hc.amb μ ⟨_, hz1 z⟩ z' (fun g => by
        show _ = (φ (z : MonoidAlgebra ℂ (G0g N.nd))).coeff (e (eR g))
        exact (hz g).trans (hφ _ _).symm) xx
      rw [cen_transport hP hA e he μ z ⟨_, hz1 z⟩ (fun g => hφ _ g)]
      exact h1
    · have h1 := hc.mt μ j ⟨_, hz1 z⟩ z' (fun g => by
        show _ = (φ (z : MonoidAlgebra ℂ (G0g N.nd))).coeff (e (eR g))
        exact (hz g).trans (hφ _ _).symm) xx
      rw [cen_transport₂ hP hM e he μ j z ⟨_, hz1 z⟩ (fun g => hφ _ g)]
      exact h1

end GlobalTheory.Mem.R3.Rw.SwapN
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeGaloisStage_fits_of_same_centre_actions : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (N : NStage B w.C (P.q.W x.o.η x.o.hη)), GrpTrue N f → N.nd.PlG = x.o.N.nd.PlG → HEq N.naut.plGw x.o.N.naut.plGw → HEq N.ntypes.cenAmb x.o.N.ntypes.cenAmb → HEq N.ntypes.cenMt x.o.N.ntypes.cenMt → GrpAt (w.st (RowPk.Over.Z (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over))) w.I ∧ ∀ eR, StdIso (w.st (RowPk.Over.Z (⟨x.o.η, x.o.hη, x.o.V, x.o.S, N, x.o.G⟩ : P.q.Over))) w.px eR → CenIs P.q.p N eR := by
  atlas_forward_decl GlobalTheory.Mem.R3.Rw.SwapN.fits_swap
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

noncomputable section

namespace GlobalTheory.HeightCounting.Up

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

def nOfLay {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P)
    (L : Lay0 (Dof x)) (hZ : L.ZOk) (hE : L.EtaOk) : NStage B w.C (P.q.W x.o.η x.o.hη) :=
  { loc := L.loc, locA := L.locA, locT := L.locT, nd := L.nd, ntw := L.ntw, naut := L.naut, nbc := L.nbc, nexp := L.nexp,
    ntypes := L.ntypes, nStage_trivialCharacter_compat := L.nStage_trivialCharacter_compat, nStage_trivialCharacter_coeff_eq := L.nStage_trivialCharacter_coeff_eq, nth := L.nth, nbr := L.nbr, nbr_ind := L.nbr_ind,
    self_good := L.self_good, ntwbr := L.ntwbr, ntwbr_ind := L.ntwbr_ind, loc_tie := L.loc_tie, bc_tie := L.bc_tie,
    rbar_tie := L.rbar_tie, mtpar_tie := L.mtpar_tie, Z_tie := hZ.1, Zgood_tie := hZ.2, etaJ_tie := hE }

theorem exists_pq_sel (B : Base) {px : PreX B.toPre} (I : ColIn B px) (hI : I.Ok) :
    ∃ Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield B.host.E)) → PlE B.host,
      (∀ v, NG.OverPl (Pq v) v) ∧ Set.range Pq = Set.range I.sel :=
  ⟨I.sel, fun v => hI.sel_ok v, rfl⟩

theorem sa_of_prN : PrN → PhtCmp → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, SA hL := by
  intro hP hC hL
  have hE := GlobalTheory.T.ray_prime_host_integral hP
  have hR := GlobalTheory.T.row_depth_of_primitive hP
  have hA := GlobalTheory.T.types_true_of_ray_class hL hP.what₂.fin hP.what₂.berger hP.greenC hP.what₂.art hP.ray hP.what₂.cheb
  unfold SA AllSt
  refine StepW.trans (StepW.and hE hR) (StepW.of_all ?_)
  intro K B f T w _ _ hq P x hLoc
  obtain ⟨hEl, hRw⟩ := hq
  obtain ⟨hElem, -, -, h, jE, hfr, hray⟩ := hEl P x
  have e1 : (cfOf x).P = f.P := by
    show w.I.C.P = f.P
    rw [w.C_eq]
  have e2 : (cfOf x).W = f.W := by
    show w.I.C.W = f.W
    rw [w.C_eq]
  have hTy : TypesTrue (Dof x).ntypes (cfOf x).P (cfOf x).W := by
    rw [e1, e2]
    exact x.fits.grp
  obtain ⟨L, hZ, hη, A, hcg, hau, hrow, hTT, hPlG, hplGw, hcA, hcM, hζ, hloc, hO1, hO2, hO3, hO4, hlab⟩ :=
    hA (Dof x) hLoc (cfOf x) jE (repOf x.r.Y) hElem.int hTy (hRw P x) hray
  have hG : GrpTrue (nOfLay x L hZ hη) f := by
    show TypesTrue L.ntypes f.P f.W
    rw [← e1, ← e2]
    exact hTT
  obtain ⟨hGA, hCen⟩ := GlobalTheory.T.heckeGaloisStage_fits_of_same_centre_actions x (nOfLay x L hZ hη) hG hPlG hplGw hcA hcM
  obtain ⟨x', hx', hrep⟩ := GlobalTheory.T.exists_transported_state_heckeGaloisStage x (nOfLay x L hZ hη) hG hGA hCen
  obtain ⟨Pq, hPq1, hPq2⟩ := exists_pq_sel B w.I w.ok
  have hEl' := hEl P x'
  have hRw' := hRw P x'
  obtain ⟨o', fits', G_eq', etaF', bk', m', copy', coh', s', r', pin'⟩ := x'
  dsimp only at hx'
  subst hx'
  obtain ⟨fr, hfrj⟩ := omFrame_exists_with_jE (setK (Dof x) L hZ hη) jE
  obtain ⟨Wd, hWd⟩ := PhtExt.exists_phtOn_all hC (setK (Dof x) L hZ hη) fr A.wdT A.wd
  let A' : SideA (setK (Dof x) L hZ hη) (cfK L hZ hη (cfOf x)) jE := { A with wd := Wd }
  have e := eq_of_heq hrep
  obtain ⟨cg⟩ := hcg
  refine ⟨⟨⟨x.o.η, x.o.hη, x.o.V, x.o.S, nOfLay x L hZ hη, x.o.G⟩, fits', G_eq', etaF', bk', m', copy', coh', s', r', pin'⟩, ⟨⟨⟨⟨h.fr, h.jLL, h.embLL⟩, jE, hfr, A', cg, hau, ?_, fr, hfrj, hWd, hRw', hEl'.1, hEl'.2.1, hlab, hζ, hEl'.2.2.1⟩,
    Pq, hPq1, hPq2⟩⟩, ⟨rfl, HEq.rfl, hloc.symm, hO1.symm, hO2.symm, hO3.symm, hO4.symm, heq_of_eq hPlG.symm⟩⟩
  rw [e]
  exact hrow

end GlobalTheory.HeightCounting.Up

end
end
