import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ThetaSeriesTies
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ResidueInjectivityAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SplitOffBadOfSuppSplitOff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NablaDeltaOperatorLatticePreserved
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeExtensionAlongFieldEmbeddingDuals
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualLatticeIsLatticeAndHermitianDual
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec

section
namespace GlobalTheory

theorem dualFrLattice_holds : Formalism.L2.DIV.DualFrLattice :=
  GlobalTheory.DualLat.dualFr_lattice_and_hdual.1

end GlobalTheory
end

section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TraceClassRank

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT
open GlobalTheory.FormTies GlobalTheory.OnTies
open Formalism.HermitianLatticesTheory (localization₂)
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Lat

theorem fg_of_graph {R P X : Type} [CommRing R] [IsNoetherianRing R] [AddCommGroup P] [Module R P] [AddCommGroup X]
    [Module R X] {N : Submodule R P} (hN : N.FG) (Γ : Submodule R (P × X)) (hΓ : ∀ x, ((0 : P), x) ∈ Γ → x = 0)
    {s : Set X} (hs : ∀ x ∈ s, ∃ p ∈ N, (p, x) ∈ Γ) : (Submodule.span R s).FG := by
  have h1 : (Γ ⊓ N.comap (LinearMap.fst R P X)).FG := by
    refine Submodule.fg_of_fg_map_of_fg_inf_ker (LinearMap.fst R P X) (hN.of_le ?_) ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact hy.2
    · have : Γ ⊓ N.comap (LinearMap.fst R P X) ⊓ LinearMap.ker (LinearMap.fst R P X) = ⊥ := by
        refine eq_bot_iff.2 ?_
        rintro ⟨p, x⟩ ⟨⟨h, -⟩, hp⟩
        have hp' : p = 0 := hp
        subst hp'
        rw [hΓ x h]
        exact Submodule.zero_mem _
      rw [this]
      exact Submodule.fg_bot
  refine (h1.map (LinearMap.snd R P X)).of_le (Submodule.span_le.2 fun x hx => ?_)
  obtain ⟨p, hp, h⟩ := hs x hx
  exact ⟨(p, x), ⟨h, hp⟩, rfl⟩

variable {K : Type} [Field K] [NumberField K] {n n' : ℕ}



theorem localization_comap_le (v : HeightOneSpectrum (𝓞 K)) (f : (Fin n → K) →ₗ[K] (Fin n' → K))
    {A B : Submodule (𝓞 K) (Fin n' → K)} (h : localization₂ v.asIdeal A ≤ localization₂ v.asIdeal B) :
    localization₂ v.asIdeal (A.comap (f.restrictScalars (𝓞 K))) ≤ localization₂ v.asIdeal (B.comap (f.restrictScalars (𝓞 K))) := by
  rintro x ⟨s, hs, hx⟩
  obtain ⟨t, ht, hy⟩ := h (x := f x) ⟨s, hs, (f.restrictScalars (𝓞 K)).map_smul s x ▸ (hx : (f.restrictScalars (𝓞 K)) (s • x) ∈ A)⟩
  exact ⟨t, ht, by rwa [Submodule.mem_comap, map_smul]⟩

end Lat

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Adelic

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)

def dataLevel (Q : Finset (Pl D.host.E)) : Subgroup (Bridge.Gf (Vc D i)) :=
  (levEnv (Vc D i) (R.βV i) (Lev.datY _ D.R.r D.R.t 1 (r_le_V i) R.Pg Q (LevelP.triv _ _ _) (fun _ _ => 1) (fun _ => 1)
    Lev.Frm.A)).J

variable {i} in

def MeetsClasses (J : Subgroup (Bridge.Gf (Vc D i))) {Cl : Type} (h : Cl → GA D (Vc D i)) : Prop :=
  (∀ c, h c ∈ GfC (Vc D i)) ∧
    ∀ x : Bridge.Gf (Vc D i), ∃ (c : Cl) (γ : GQ (Vc D i)) (k : J), x = Bridge.ratF (Vc D i) γ * fin (Vc D i) (h c) * k

def seriesAt (U : Subgroup G) (ψ : U →* D.what₂.LLˣ) (ph : ℂ) (ω : WeilRep D i) (φ : Datum.WO (Vc D i) (Wc D i) → ℂ)
    (h : GA D (Vc D i)) : Set (Fin (R.nW i) → D.what₂.LL) :=
  {x | ∃ w, InCoefLat R i h w ∧ ∀ v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ,
    adForm R i x (fun ρ => v ρ) = ph • levelTrace R i U ψ (singleSeries R i ω φ h w v)}

def IsBaseKernel (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (p : ℕ) (ω : WeilRep D i) (φ : Datum.WO (Vc D i) (Wc D i) → ℂ) : Prop :=
  IsKernel R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) (placesOver R (R.mu v) p) ω φ

def SpanOverClasses (U : Subgroup G) (ψ : U →* D.what₂.LLˣ) (ph : ℂ) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (p : ℕ) : Prop :=
  ∀ ω φ, IsBaseKernel R i v p ω φ → ∀ (Cl : Type) (h : Cl → GA D (Vc D i)),
    MeetsClasses (dataLevel R i (placesOver R (R.mu v) p)) h →
      thetaBase R i U ψ ph v p = Submodule.span (𝓞 D.what₂.LL) (⋃ c, seriesAt R i U ψ ph ω φ (h c))

abbrev goodOp : (Fin (R.nW i) → D.what₂.LL) →ₗ[D.what₂.LL] (Fin (R.nW i) → D.what₂.LL) :=
  (R.FW i).eOp fun g => (idemOf A.X).coeff g

abbrev goodType (U : Subgroup G) (ψ : U →* D.what₂.LLˣ) : Submodule D.what₂.LL (Fin (R.nW i) → D.what₂.LL) :=
  (R.FW i).Wgood U ψ fun g => (idemOf A.X).coeff g

def ClassFullRank (U : Subgroup G) (ψ : U →* D.what₂.LLˣ) (ph : ℂ) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (p : ℕ) : Prop :=
  Submodule.span D.what₂.LL ((thetaBase R i U ψ ph v p).map ((goodOp R i).restrictScalars (𝓞 D.what₂.LL)) :
    Set (Fin (R.nW i) → D.what₂.LL)) = goodType R i U ψ

def FormsDetermined : Prop :=
  ∀ x, (∀ v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, adForm R i x (fun ρ => v ρ) = 0) → x = 0

def BaseKernelUnique (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (p : ℕ) : Prop :=
  ∀ ω φ ω' φ', IsBaseKernel R i v p ω φ → IsBaseKernel R i v p ω' φ' → singleSeries R i ω φ = singleSeries R i ω' φ'

def KernelSpanOverClasses (U : Subgroup G) (ψ : U →* D.what₂.LLˣ) (ph : ℂ) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (p : ℕ) : Prop :=
  ∀ ω φ, IsBaseKernel R i v p ω φ → ∀ (Cl : Type) (h : Cl → GA D (Vc D i)),
    MeetsClasses (dataLevel R i (placesOver R (R.mu v) p)) h →
      Submodule.span (𝓞 D.what₂.LL) (seriesSet R i U ψ ph ω φ) =
        Submodule.span (𝓞 D.what₂.LL) (⋃ c, seriesAt R i U ψ ph ω φ (h c))

variable {R i}

theorem spanOverClasses_of {U : Subgroup G} {ψ : U →* D.what₂.LLˣ} {ph : ℂ} {v : HeightOneSpectrum (𝓞 D.what₂.LL)} {p : ℕ}
    (h1 : BaseKernelUnique R i v p) (h2 : KernelSpanOverClasses R i U ψ ph v p) : SpanOverClasses R i U ψ ph v p := by
  intro ω φ hk Cl h hh
  rw [← h2 ω φ hk Cl h hh]
  unfold thetaBase
  congr 1
  ext x
  refine ⟨?_, fun hx => ⟨ω, φ, hk, hx⟩⟩
  rintro ⟨ω', φ', hk', hx⟩
  unfold seriesSet at hx ⊢
  rwa [h1 ω φ ω' φ' hk hk']

theorem formsDetermined_of (hres : GlobalTheory.IndefiniteRowSideFullHecke.ResidueInjectivityAt.ResInjAt R) (hW : R.models_HW) (hu : R.LUnif) : FormsDetermined R i := by
  intro x hx
  obtain ⟨h1, h2, -⟩ := hW i (sg0 D A)
  have h3 : adForm R i x = 0 := hres i _ (h2 ▸ LinearMap.mem_range_self _ _) hx
  have h4 : (R.FW i).j (sg0 D A) x = 0 := h1 (h3.trans (map_zero _).symm)
  by_contra h0
  have h5 := (hu i (sg0 D A)).1 1 (fun _ => x) (linearIndependent_unique_iff.2 h0)
  exact h5.ne_zero 0 h4

theorem levJ_le_dataLevel (t : T0) {Q : Finset (Pl D.host.E)} (hQ : Q ⊆ R.Q t) : levJ R i t ≤ dataLevel R i Q := by
  intro x hx
  exact ⟨⟨hx.1.1, Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP =>
    Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hx.1.2 PP) (hQ hP)⟩, hx.2⟩

theorem nabAtr_hLat_fg (g : Bridge.Gf (Vc D i)) : (nabAtr (labLL D) (lamV D i) (Bridge.hLat (Vc D i) g)).FG :=
  (GlobalTheory.TransLattice.nabDelLattice _ _ _ _ _ fun τ => (GlobalTheory.dualFrLattice_holds D.what₂.LL _ 1 _ (by simp)
    (GlobalTheory.TauLat.tauLatLattice _ _ _ _ (labLL D) τ _ (GlobalTheory.RepsCompare.isLattice_hLat _ g))).1).1.fg

theorem coefTie_class {V : HSp D} {C : Bridge.CoefDat D V} {S : CSD D.what₂.LL} {J : Subgroup (Bridge.Gf V)} {χ : J →* ℂˣ}
    {P : Bridge.ClassPres (Bridge.ratF V) S D.what₂.embLL C.ρ J χ} {lam : D.what₂.Tau → DomWeight V.rank}
    {c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] C.W}
    {pair : VV D.what₂.LL lam →ₗ⋆[D.what₂.LL] VV D.what₂.LL lam →ₗ[D.what₂.LL] D.what₂.LL}
    {nab del : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) → Submodule (𝓞 D.what₂.LL) (VV D.what₂.LL lam)}
    (h : Bridge.CoefTie V C P lam c0 pair nab del) (c : S.Cl) :
    ((nab (Bridge.hLat V (P.y c))).FG → (S.Nab c).FG) ∧
      ∀ x ∈ nab (Bridge.hLat V (P.y c)), ∃ y ∈ S.Nab c, c0 x = P.coef y := by
  obtain ⟨e, -, h2, -, h4, -⟩ := h
  refine ⟨fun hf => ?_, fun x hx => ?_⟩
  · rw [← h4 c] at hf
    exact Submodule.fg_of_fg_map_injective (e.toLinearMap.restrictScalars (𝓞 D.what₂.LL)) e.injective hf
  · rw [← h4 c] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨y, hy, (h2 y).symm⟩

theorem exists_coef_fg (t : T0) (c : (A.MtCSD i t).Cl) {h : GA D (Vc D i)} (hh : fin (Vc D i) h = (R.B.L i t).pres.y c) :
    ∃ N : Submodule (𝓞 D.what₂.LL) (A.MtCSD i t).V, N.FG ∧
      ∀ w, InCoefLat R i h w → ∃ P ∈ N, w = (R.B.L i t).pres.coef P := by
  by_cases hex : ∃ w, InCoefLat R i h w
  · obtain ⟨-, gramR, c0R, c0L, hT, -⟩ := hex
    refine ⟨(A.MtCSD i t).Nab c, ?_, ?_⟩
    · exact (coefTie_class (hT.coefL i t) c).1 (nabAtr_hLat_fg _)
    · rintro w ⟨gramR', c0R', c0L', hT', P, hP, rfl⟩
      rw [hh] at hP
      exact (coefTie_class (hT'.coefL i t) c).2 P hP
  · exact ⟨⊥, Submodule.fg_bot, fun w hw => absurd ⟨w, hw⟩ hex⟩

theorem singleSeries_add (ω : WeilRep D i) (φ : Datum.WO (Vc D i) (Wc D i) → ℂ) (h : GA D (Vc D i)) (w w' : (R.cV i).W)
    (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) :
    singleSeries R i ω φ h (w + w') v = singleSeries R i ω φ h w v + singleSeries R i ω φ h w' v := by
  funext g
  simp only [singleSeries, Datum.thetaKO, map_add, Pi.add_apply]

theorem singleSeries_smul (ω : WeilRep D i) (φ : Datum.WO (Vc D i) (Wc D i) → ℂ) (h : GA D (Vc D i)) (a : ℂ) (w : (R.cV i).W)
    (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) :
    singleSeries R i ω φ h (a • w) v = a • singleSeries R i ω φ h w v := by
  funext g
  simp only [singleSeries, Datum.thetaKO, map_smul, Pi.smul_apply]

theorem adForm_add (x y : Fin (R.nW i) → D.what₂.LL) : adForm R i (x + y) = adForm R i x + adForm R i y := by
  unfold adForm
  rw [map_add, map_add]

theorem adForm_smul (a : D.what₂.LL) (x : Fin (R.nW i) → D.what₂.LL) : adForm R i (a • x) = D.what₂.embLL a • adForm R i x := by
  unfold adForm
  rw [LinearMap.map_smulₛₗ, map_smul]
  congr 1
  exact RingHom.congr_fun (sgAt_mk _ R.hv0) a

theorem seriesAt_fg (hd : FormsDetermined R i) (U : Subgroup G) (ψ : U →* D.what₂.LLˣ) (ph : ℂ) (ω : WeilRep D i)
    (φ : Datum.WO (Vc D i) (Wc D i) → ℂ) (t : T0) (c : (A.MtCSD i t).Cl) {h : GA D (Vc D i)}
    (hh : fin (Vc D i) h = (R.B.L i t).pres.y c) : (Submodule.span (𝓞 D.what₂.LL) (seriesAt R i U ψ ph ω φ h)).FG := by
  obtain ⟨N, hN, H⟩ := exists_coef_fg t c hh
  let cf : (A.MtCSD i t).V →ₛₗ[D.what₂.embLL] (R.cV i).W := (R.B.L i t).pres.coef
  let Γ : Submodule D.what₂.LL ((A.MtCSD i t).V × (Fin (R.nW i) → D.what₂.LL)) :=
    { carrier := {q | ∀ v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ,
        adForm R i q.2 (fun ρ => v ρ) = ph • levelTrace R i U ψ (singleSeries R i ω φ h (cf q.1) v)}
      add_mem' := fun {a b} ha hb v => by
        rw [Prod.fst_add, Prod.snd_add, adForm_add, map_add, singleSeries_add, map_add, smul_add, ← ha v, ← hb v]
        rfl
      zero_mem' := fun v => by
        have h1 := adForm_smul (R := R) (i := i) 0 0
        have h2 := singleSeries_smul (R := R) ω φ h 0 0 v
        rw [zero_smul, map_zero, zero_smul] at h1
        rw [zero_smul, zero_smul] at h2
        rw [Prod.fst_zero, Prod.snd_zero, h1, map_zero, h2, map_zero, smul_zero]
        rfl
      smul_mem' := fun a q hq v => by
        rw [Prod.smul_fst, Prod.smul_snd, adForm_smul, LinearMap.map_smulₛₗ, singleSeries_smul, map_smul, smul_comm, ← hq v]
        rfl }
  refine fg_of_graph hN (Γ.restrictScalars (𝓞 D.what₂.LL)) (fun x hx => hd x fun v => ?_) ?_
  · have h2 := singleSeries_smul (R := R) ω φ h 0 0 v
    rw [zero_smul, zero_smul] at h2
    have h3 : adForm R i x (fun ρ => v ρ) = ph • levelTrace R i U ψ (singleSeries R i ω φ h (cf 0) v) := hx v
    rw [h3, map_zero, h2, map_zero, smul_zero]
  · rintro x ⟨w, hw, hx⟩
    obtain ⟨P, hP, rfl⟩ := H w hw
    exact ⟨P, hP, hx⟩

theorem thetaBase_fg (hd : FormsDetermined R i) {U : Subgroup G} {ψ : U →* D.what₂.LLˣ} {ph : ℂ}
    {v : HeightOneSpectrum (𝓞 D.what₂.LL)} {p : ℕ} (hM : SpanOverClasses R i U ψ ph v p) : (thetaBase R i U ψ ph v p).FG := by
  classical
  by_cases hex : ∃ ω φ, IsBaseKernel R i v p ω φ
  · obtain ⟨ω, φ, hk⟩ := hex
    choose h hh using fun c => (GlobalTheory.RepsCompare.existsUnique_lift (Vc D i) ((R.B.L i (R.mu v)).pres.y c)).exists
    rw [hM ω φ hk _ h ⟨fun c => (hh c).1, fun x => ?_⟩, Submodule.span_iUnion]
    · exact Submodule.fg_iSup _ fun c => seriesAt_fg hd U ψ ph ω φ _ c (hh c).2
    · obtain ⟨c, γ, k, e⟩ := ((R.B.L i (R.mu v)).pres.reps x).exists
      exact ⟨c, γ, ⟨k, levJ_le_dataLevel (R.mu v) (Finset.filter_subset _ _) k.2⟩, by rw [(hh c).2]; exact e⟩
  · have : thetaBase R i U ψ ph v p = ⊥ := Submodule.span_eq_bot.2 fun x ⟨ω, φ, hk, _⟩ => absurd ⟨ω, φ, hk⟩ hex
    rw [this]
    exact Submodule.fg_bot

end Adelic

end GlobalTheory.TraceClassRank
end
end

section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TraceClassRank

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT
open GlobalTheory.FormTies GlobalTheory.OnTies
open Formalism.HermitianLatticesTheory (localization₂)
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Trace

variable {T : Full D} [inst : Algebra T.J.Q.c.F D.what₂.LL] {R : RealDat D A T.J.Q.c.F}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
  (h : LawsP T.toTop) (fw : FWTie T.J R κ v₀) (ι : Fin D.R.m)
  (ℓ : G → (LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l))
  (U : Subgroup G) (ψ : U →* D.what₂.LLˣ) (ph : ℂ) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (p : ℕ)

def traceLat : Submodule (𝓞 D.what₂.LL) (Fin (R.nW ι) → D.what₂.LL) :=
  Submodule.span (𝓞 D.what₂.LL)
    ((fun f : U → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι) =>
        ∑ᶠ u : U, ((ψ u : D.what₂.LLˣ) : D.what₂.LL) • cuspTo h fw ι (f u)) ''
      {f | IsOrbitFamily (T.Q.Xo ((ι : ℕ) + 1)) T.Q.c (badN D) (wtA (κ ι)) (T.dδ ((ι : ℕ) + 1) (κ ι).n) (fun u : U => ℓ u)
        fun u => ((f u).1 : T.R ((ι : ℕ) + 1))})

def CompareAt (lam : HeightOneSpectrum (𝓞 D.what₂.LL)) : Prop :=
  localization₂ lam.asIdeal (traceLat h fw ι ℓ U ψ) ≤ localization₂ lam.asIdeal (thetaBase R ι U ψ ph v p)

def CompareOffOwn : Prop := ∀ lam, Formalism.EigenvalueLevelCeiling.plc lam ≠ p → CompareAt h fw ι ℓ U ψ ph v p lam

def CompareSpan : Prop :=
  Submodule.span D.what₂.LL (traceLat h fw ι ℓ U ψ : Set (Fin (R.nW ι) → D.what₂.LL)) =
    Submodule.span D.what₂.LL (thetaBase R ι U ψ ph v p : Set (Fin (R.nW ι) → D.what₂.LL))

def CompareAtOwn : Prop := ∀ lam, Formalism.EigenvalueLevelCeiling.plc lam = p → CompareAt h fw ι ℓ U ψ ph v p lam

variable {h fw ι ℓ U ψ ph v p} {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D}
    {wL wF : WeightFamilies.Wt D ((ι : ℕ) + 1)} {nT : ℕ}
    {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {oc : OnConst}
    {O : OnObj S P oc} {i : Bs.J}
    {z : (Fin (O.nZ i) → D.what₂.LL) ≃ₗ[D.what₂.LL]
      D.what₂.LL ⊗[(recB h.toLawsCore).KO] (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι)}
    {act : P → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι) → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι)}
    {inc : P →* G}
    {y : (Fin (O.nX v i) → D.what₂.LL) ≃ₗ[D.what₂.LL] (Fin (srcDim A ι (R.mu v) U ψ) → D.what₂.LL)}


def comapEquiv {P G : Type} [Group P] [Group G] {inc : P →* G} (hi : Function.Injective inc) {U : Subgroup G}
    (hU : U ≤ inc.range) : U.comap inc ≃ U :=
  Equiv.ofBijective (fun u => ⟨inc u, u.2⟩) ⟨fun _ _ e => Subtype.ext (hi (congrArg Subtype.val e)), fun u => by
    obtain ⟨g, hg⟩ := hU u.2
    exact ⟨⟨g, show inc g ∈ U from hg ▸ u.2⟩, Subtype.ext hg⟩⟩

theorem isOrbitFamily_comp {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l}
    {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {bad : ℕ} {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {d : DeltaDat Xo c n} {I I' : Type}
    {m : I → (LaMod Dw l ≃ₗ[𝓞 E] LaMod Dw l)} {m' : I' → (LaMod Dw l ≃ₗ[𝓞 E] LaMod Dw l)}
    {f : I → Rul Xo c} (hf : IsOrbitFamily Xo c bad a d m f) (e : I' → I) (he : ∀ u, m' u = m (e u)) :
    IsOrbitFamily Xo c bad a d m' fun u => f (e u) := by
  obtain ⟨Λ, N, x₀, P, x, h1, h2, h3, h4, h5, h6, h7⟩ := hf
  exact ⟨Λ, N, x₀, P, fun u => x (e u), h1, h2, h3, h4, h5, h6, fun u => he u ▸ h7 (e u)⟩

abbrev coordEquiv (h : LawsP T.toTop) (fw : FWTie T.J R κ v₀) (ι : Fin D.R.m) {n : ℕ}
    (z : (Fin n → D.what₂.LL) ≃ₗ[D.what₂.LL]
      D.what₂.LL ⊗[(recB h.toLawsCore).KO] (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι)) :
    (Fin n → D.what₂.LL) ≃ₗ[D.what₂.LL] (Fin (R.nW ι) → D.what₂.LL) :=
  LinearEquiv.ofBijective (toForms h fw ι z) (toForms_bijective h fw ι z)

theorem Th0_eq_comap (t : OnTie h fw hinj EX p ι wL wF nT O v i z act inc ℓ U ψ ph y) (hi : Function.Injective inc)
    (hU : U ≤ inc.range) :
    O.Th0 v i = (traceLat h fw ι ℓ U ψ).comap ((toForms h fw ι z).restrictScalars (𝓞 D.what₂.LL)) := by
  have hm : (O.Th0 v i).map ((toForms h fw ι z).restrictScalars (𝓞 D.what₂.LL)) = traceLat h fw ι ℓ U ψ := by
    rw [t.Th0_eq, t.U_eq]
    unfold thetaEig traceSpan traceLat
    rw [Submodule.map_span, Set.image_image]
    have key : ∀ f : U → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι),
        (toForms h fw ι z).restrictScalars (𝓞 D.what₂.LL)
          (∑ᶠ u : U.comap inc, O.ψ (u : P) • z.symm (1 ⊗ₜ[(recB h.toLawsCore).KO] f (comapEquiv hi hU u))) =
        ∑ᶠ u : U, ((ψ u : D.what₂.LLˣ) : D.what₂.LL) • cuspTo h fw ι (f u) := fun f => by
      rw [map_finsum _ (Set.toFinite _), ← finsum_comp_equiv (comapEquiv hi hU)]
      refine finsum_congr fun u => ?_
      rw [map_smul, LinearMap.restrictScalars_apply, toForms_tmul, one_smul, ← algebraMap_smul D.what₂.LL]
      exact congrArg (· • _) (t.ψ_eq u u.2)
    congr 1
    ext x
    constructor
    · rintro ⟨f, hf, rfl⟩
      refine ⟨fun u => f ((comapEquiv hi hU).symm u), isOrbitFamily_comp hf _ (fun u => ?_), ?_⟩
      · exact congrArg (fun a : U => ℓ a) ((comapEquiv hi hU).apply_symm_apply u).symm
      · refine (key _).symm.trans ?_
        simp only [Equiv.symm_apply_apply]
    · rintro ⟨f, hf, rfl⟩
      exact ⟨fun u => f (comapEquiv hi hU u), isOrbitFamily_comp hf _ fun u => rfl, key f⟩
  rw [← hm]
  exact (Submodule.comap_map_eq_of_injective (f := (toForms h fw ι z).restrictScalars (𝓞 D.what₂.LL))
    (toForms_bijective h fw ι z).1 _).symm




theorem trace_lattice_le_theta_lattice_at_place (t : OnTie h fw hinj EX p ι wL wF nT O v i z act inc ℓ U ψ ph y) (hi : Function.Injective inc)
    (hU : U ≤ inc.range) {n : ℕ} (hp : RunPin R ι n v p) (hA : CompareOffOwn h fw ι ℓ U ψ ph v p) :
    localization₂ v.asIdeal (O.Th0 v i) ≤ localization₂ v.asIdeal (O.ThJ v i) := by
  rw [Th0_eq_comap t hi hU, t.ThJ_eq]
  refine localization_comap_le v _ (hA v fun e => ?_)
  have h1 := hp.1
  split_ifs at h1 with h2
  · exact D.host.pde_ne (h2.symm.trans (e.trans h1))
  · exact h2 (e.trans h1)


end Trace

section Place

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {P : Type}
  [Group P] [Finite P] {c : OnConst}

def RankAtPlaces (O : OnObj S P c) : Prop :=
  AtPair S fun v => ∀ j, Formalism.EigenvalueLevelCeiling.IsLatIn (O.Zg j) ((O.Th0 v j).map ((O.e j).restrictScalars (𝓞 K))) ∧
    Formalism.EigenvalueLevelCeiling.IsLatIn (O.Zg j) (O.eJ v j) ∧ localization₂ v.asIdeal (O.Th0 v j) ≤ localization₂ v.asIdeal (O.ThJ v j)

def fillJ (O : OnObj S P c) : OnObj S P c := { O with ThJ := fun v j => O.ThJ v j ⊔ O.Th0 v j }


theorem leafRankJ_fillJ {O : OnObj S P c} (h : RankAtPlaces O) : LeafRankJ (fillJ O) := by
  have key : ∀ v j, Formalism.EigenvalueLevelCeiling.IsLatIn (O.Zg j) ((O.Th0 v j).map ((O.e j).restrictScalars (𝓞 K))) →
      Formalism.EigenvalueLevelCeiling.IsLatIn (O.Zg j) (O.eJ v j) → Formalism.EigenvalueLevelCeiling.IsLatIn (O.Zg j) ((fillJ O).eJ v j) := fun v j a b => by
    change Formalism.EigenvalueLevelCeiling.IsLatIn _ ((O.ThJ v j ⊔ O.Th0 v j).map ((O.e j).restrictScalars (𝓞 K)))
    rw [Submodule.map_sup]
    refine ⟨b.1.sup a.1, le_antisymm (Submodule.span_le.2 ?_) ?_⟩
    · change _ ≤ (O.Zg j).restrictScalars (𝓞 K)
      exact sup_le (fun x hx => b.2.le (Submodule.subset_span hx)) fun x hx => a.2.le (Submodule.subset_span hx)
    · exact b.2.ge.trans (Submodule.span_mono (show O.eJ v j ≤ _ from le_sup_left))
  exact fun w hw =>
    ⟨fun j => ⟨((h w hw).1 j).1, key _ j ((h w hw).1 j).1 ((h w hw).1 j).2.1, le_sup_right⟩,
      fun j => ⟨((h w hw).2 j).1, key _ j ((h w hw).2 j).1 ((h w hw).2 j).2.1, le_sup_right⟩⟩

theorem lix_fillJ {O : OnObj S P c} {v : HeightOneSpectrum (𝓞 K)} {j : Bs.J}
    (h : localization₂ v.asIdeal (O.Th0 v j) ≤ localization₂ v.asIdeal (O.ThJ v j)) (M : Submodule (𝓞 K) (Fin (O.nZ j) → K)) :
    Formalism.EigenvalueLevelCeiling.lix v M ((fillJ O).eJ v j) = Formalism.EigenvalueLevelCeiling.lix v M (O.eJ v j) := by
  have h1 : O.ThJ v j ⊔ O.Th0 v j ≤ localization₂ v.asIdeal (O.ThJ v j) :=
    sup_le (Formalism.HermitianLatticesTheory.locBasic_le_locS _ _) ((Formalism.HermitianLatticesTheory.locBasic_le_locS _ _).trans h)
  have h2 : (fillJ O).eJ v j ≤ localization₂ v.asIdeal (O.eJ v j) := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨s, hs, hsx⟩ := h1 hx
    exact ⟨s, hs, _, hsx, map_smul ((O.e j).restrictScalars (𝓞 K)) s x⟩
  have h3 : localization₂ v.asIdeal ((fillJ O).eJ v j) = localization₂ v.asIdeal (O.eJ v j) :=
    le_antisymm ((Formalism.HermitianLatticesTheory.locBasic_locS_mono _ h2).trans (Formalism.HermitianLatticesTheory.locBasic_locS_idem _ _).le)
      (Formalism.HermitianLatticesTheory.locBasic_locS_mono _ (Submodule.map_mono le_sup_left))
  exact (Formalism.EigenvalueLevelCeiling.lix_locP v M _).trans ((congrArg _ h3).trans (Formalism.EigenvalueLevelCeiling.lix_locP v M _).symm)

theorem leafTW1_fillJ {O : OnObj S P c} (h : RankAtPlaces O) (h1 : LeafTW1 O) : LeafTW1 (fillJ O) :=
  ⟨fun w hw =>
    ⟨fun j => ⟨((h1.1 w hw).1 j).1, ((h1.1 w hw).1 j).2.trans_eq
        (congrArg (fun a : ℤ => (a : ℝ) + _) (lix_fillJ ((h w hw).1 j).2.2 _).symm)⟩,
      fun j => ⟨((h1.1 w hw).2 j).1, ((h1.1 w hw).2 j).2.trans_eq
        (congrArg (fun a : ℤ => (a : ℝ) + _) (lix_fillJ ((h w hw).2 j).2.2 _).symm)⟩⟩, h1.2⟩

theorem on_core_atPlaces (N : IndefNum Bs) (O : OnObj S P c) (CE : ℝ) (hRk : RankRows S)
    (hMk : LeafMackey O) (hSup : LeafSup O) (hProj : LeafProj O) (hC : TieCoord O)
    (hSp : LeafSpan O) (hS : LeafLemmaS O) (hT0 : LatticeIndexBoundAtPairs O) (hD : LeafData O) (hJ : RankAtPlaces O)
    (hI : LeafIdentity O) (h2 : LeafTW2 O) (h1 : LeafTW1 O)
    (hSh : LeafShareI O) (hIU : LeafIndexU O) (hBS : LeafBadShare O) (hUn : LeafUnip O)
    (hG : LeafDepthGood N O) (hR : LeafDepthRam N O) (h2p : LeafDepth2 N O) (hL : LeafDepthLevel N O)
    (hPg : LeafPage O) (hSz : LeafSizes O) (hX : LeafX O) (hBad : LeafBad O)
    (hJS : LeafJSum O) (hJE : LeafJExp N O) (hCE : c.CE ≤ CE) (tE1 : ErrorConstantMatchesDefinition N O CE) : ONwith S N O.errOn :=
  on_core N (fillJ O) CE hRk hMk hSup hProj hC hSp hS hT0 hD (leafRankJ_fillJ hJ) hI h2 (leafTW1_fillJ hJ h1) hSh hIU hBS hUn
    hG hR h2p hL hPg hSz hX hBad hJS hJE hCE tE1

end Place

section Row

variable {T : HeightOneSpectrum (𝓞 D.what₂.LL) → Full D} [inst : ∀ v, Algebra (T v).J.Q.c.F D.what₂.LL]
  {R : ∀ v, RealDat D A (T v).J.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
  {v₀ : ∀ v (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), ((R v).MW i σ).Vec}
  {h : ∀ v, LawsP (T v).toTop} {fw : ∀ v, FWTie (T v).J (R v) κ (v₀ v)} {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D}
  {p : HeightOneSpectrum (𝓞 D.what₂.LL) → ℕ}
  {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {oc : OnConst}
  {O : OnObj S P oc} {ι : Bs.J → Fin D.R.m} {wL wF : ∀ i, WeightFamilies.Wt D ((ι i : ℕ) + 1)} {nT : ℕ}
  {z : ∀ v i, (Fin (O.nZ i) → D.what₂.LL) ≃ₗ[D.what₂.LL]
    D.what₂.LL ⊗[(recB (h v).toLawsCore).KO] (recB (h v).toLawsCore).Cusp ((ι i : ℕ) + 1) (κ (ι i))}
  {act : ∀ v i, P → (recB (h v).toLawsCore).Cusp ((ι i : ℕ) + 1) (κ (ι i)) →
    (recB (h v).toLawsCore).Cusp ((ι i : ℕ) + 1) (κ (ι i))}
  {inc : P →* G}
  {ℓ : ∀ v i, G → (LaMod ((T v).Q.Dw ((ι i : ℕ) + 1)) (T v).Q.l ≃ₗ[𝓞 D.host.E] LaMod ((T v).Q.Dw ((ι i : ℕ) + 1)) (T v).Q.l)}
  {U : Subgroup G} {ψ : U →* D.what₂.LLˣ} {ph : HeightOneSpectrum (𝓞 D.what₂.LL) → Bs.J → ℂ}
  {y : ∀ v i, (Fin (O.nX v i) → D.what₂.LL) ≃ₗ[D.what₂.LL] (Fin (srcDim A (ι i) ((R v).mu v) U ψ) → D.what₂.LL)}



end Row

end GlobalTheory.TraceClassRank
end
end
