import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharpolySmulOfProd

noncomputable section

namespace GlobalTheory.Triple.Model

open NumberField IsDedekindDomain Polynomial Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open Formalism.L2.Host (HChar CharFrame embLL0 eExp ValLL0)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
open GlobalTheory.GalChar (IsGal toQ block)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf Zbar GalE toFb)
open scoped TensorProduct

variable {D : D7}

section Indep

variable {C : CharFrame D} {art : Ideles D.host.E →* Gab D.host.E D.nd.Om} {X : NTw D.R D.host D.what₂ D.LL0 D.nd}
  {i : X.Tw} {b : Bool}




theorem notMem_l {k : Fin 2} (hk : X.l i ≠ D.host.g k) (v : D.nd.PlG k) :
    ((X.l i : ℕ) : 𝓞 D.host.E) ∉ (D.naut.plGw k v).asIdeal :=
  GlobalTheory.GalChar.notMem_of_ne (D.host.g_prime k) (X.lPrime i).out hk.symm (D.naut.plGw_over k v)


end Indep

section Tame

variable (C : CharFrame D) (art : Ideles D.host.E →* Gab D.host.E D.nd.Om)

def TameTie (c : ∀ k, D.nd.PlG k → Fin D.R.m → (ZMod (D.host.g k))ˣ) : Prop :=
  ∀ (k : Fin 2) (v : D.nd.PlG k) (l : ℕ) [Fact l.Prime], l ≠ D.host.g k →
    ∀ (O : Type) [CommRing O] [IsDomain O] [TopologicalSpace O] (κ : FractionRing O →+* Qbar l) (ι : Qbar l ≃+* ℂ)
      (j : Fin D.R.m) n (χ : GalE D →* Oˣ), IsGal art κ ι (blockChar C l j) n χ →
      ι (toQ κ ((χ (D.ntypes.tg k v) : Oˣ) : O)) = D.ntypes.teichC k (toFb D k (c k v j)⁻¹)

variable {C art}


end Tame

section Record

variable (D) (C : CharFrame D) {art : Ideles D.host.E →* Gab D.host.E D.nd.Om} (ha : IsGlobalArtin art) (hC : ValLL0 D C)
  (hs : ∀ x : ↥D.LL0, star (x : D.what₂.LL) ∈ D.LL0)

def rd (i : D.ntw.Tw) : Reading D.ntw i true := (Reading.nonempty i true).some

include hs in
theorem rd_conj (i : D.ntw.Tw) (x : ↥D.LL0) :
    (rd D i).ι ((rd D i).κ (D.ntw.emb0b i x)) = starRingEnd ℂ (embLL0 D x) :=
  GlobalTheory.GalChar.read_conj D.LL0 D.what₂.embLL D.starLL_cx hs (D.ntw.restX_coefficientEmbedding_conj i) (rd D i).read x

include hC in
theorem del_val (l : ℕ) : (C.delAt l).ValuesIn 0 (embLL0 D) := by
  unfold CharFrame.delAt
  split_ifs
  exacts [hC.del', hC.del]

structure Chars (art : Ideles D.host.E →* Gab D.host.E D.nd.Om) (i : D.ntw.Tw) where
  delta : GalE D →* (D.ntw.O0 i)ˣ
  chi1 : ℕ → Bool → (GalE D →* (D.ntw.O0 i)ˣ)
  gal : ∀ (j : Fin D.R.m) (b : Bool), ∃ n, IsGal art (rd D i).κ (GlobalTheory.GalChar.sideIso (rd D i).ι b)
    (blockChar C (D.ntw.l i) j) n (chi1 (j.1 + 1) b)
  h1 : IsOpen (delta.ker : Set (GalE D))
  h2 : AntiHom D.ntw.cc delta
  h3 : RamExactly delta ↑(D.ntw.pD i)
  h4 : ∀ v ∈ D.ntw.pD i, ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A v →
    Nat.card ((Ine (F := D.host.E) A).map delta) = 15
  h5 : ∀ j b, Continuous (fun g => ((chi1 j b g : (D.ntw.O0 i)ˣ) : D.ntw.O0 i))
  h6 : ∀ j b v, v ∉ placesOver D.host.E (D.ntw.l i) → (∀ k, v ∉ placesOver D.host.E (D.host.g k)) → v ∉ D.ntw.pD i →
    ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A v → ∀ σ ∈ Ine (F := D.host.E) A, chi1 j b σ = 1
  h7 : ∀ j b, ∀ v ∈ D.ntw.pD i, ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A v →
    ∀ σ ∈ Ine (F := D.host.E) A, chi1 j b σ = if b then delta σ else (delta σ)⁻¹
  h8 : ∀ j b k v, v ∈ placesOver D.host.E (D.host.g k) → v ∉ placesOver D.host.E (D.ntw.l i) →
    ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A v → ∀ σ ∈ Ine (F := D.host.E) A, chi1 j b σ ^ (D.host.g k - 1) = 1

include ha hC hs in
theorem chars_nonempty (i : D.ntw.Tw) : Nonempty (Chars D C art i) := by
  obtain ⟨δ, χ, -, g, h1, h2, h3, h4, -, h5, h6, h7, h8⟩ :=
    (GlobalTheory.GalChar.galois_characters_of_artin D.R D.host D.nd.Om D.ntw.cc D.ntw.cc_cm _ eExp_int (hframe C) D.nd.g_split art ha).1
      (D.ntw.l i) (D.ntw.O0 i) (D.ntw.twistBaseCoefficientRing_isAdic i) (rd D i).κ (rd D i).κ_alg (rd D i).ι ↥D.LL0 (embLL0 D) (D.ntw.emb0 i)
      (D.ntw.emb0b i) (rd D i).read (rd_conj D hs i) hC.mu0 hC.eta (del_val D C hC _) (D.ntw.pD i) (D.ntw.pD_eq i)
  exact ⟨⟨δ, χ, g, h1, h2, h3, h4, h5, h6, h7, h8⟩⟩

variable {art' : Ideles D.host.E →* Gab D.host.E D.nd.Om} (K : ∀ i, Chars D C art' i) [IsEmpty D.nd.Loc]

@[reducible] def tw : @NTw D.R D.host D.what₂ D.nfLL D.starLL D.LL0 D.nd :=
  { D.ntw with
    delta := fun i => (K i).delta
    delta_open := fun i => (K i).h1
    delta_anti := fun i => (K i).h2
    delta_ram := fun i => (K i).h3
    delta_15 := fun i => (K i).h4
    chi1 := fun i => (K i).chi1
    twistCharacterFamily_continuous := fun i => (K i).h5
    twistCharacterFamily_unramified := fun i => (K i).h6
    twistCharacterFamily_at_auxiliaryPlaces := fun i => (K i).h7
    twistCharacterFamily_tame := fun i => (K i).h8
    chi_tw := fun a => isEmptyElim a
    Sig := fun _ => Empty
    finSig := fun _ => inferInstance
    jS := fun _ e => e.elim
    jS_range := fun _ e => e.elim
    side := fun _ e => e.elim
    rhoS := fun _ e => e.elim
    rhoS_cont := fun _ e => e.elim
    hEig := fun _ e => e.elim
    B := fun _ _ _ => PUnit
    acgB := fun _ _ _ => inferInstance
    modB := fun _ _ _ => inferInstance
    freeB := fun _ _ _ => inferInstance
    finB := fun _ _ _ => inferInstance
    Theta := fun _ _ _ => ⊤
    ThetaPsi := fun _ _ _ _ _ _ => ⊤
    ThetaPsi_one := fun _ _ _ _ => (Submodule.baseChange_top _).symm
    hk := fun _ _ _ _ _ => 1
    hk_zero := fun _ _ _ _ => rfl
    abelian₂ := fun _ => Empty
    finLam := fun _ => inferInstance
    jL := fun _ e => e.elim
    sideL := fun _ e => e.elim
    s2 := fun _ e => e.elim
    jL_range := fun _ e => e.elim
    lamG := fun _ e => e.elim
    lamG_cont := fun _ e => e.elim
    lamG_unr := fun _ e => e.elim
    lamG_pD := fun _ e => e.elim
    lamG_anti := fun _ e => e.elim
    Xv := fun _ e => e.elim
    Xv_def := fun _ e => e.elim
    qs := fun _ e => e.elim
    qs_sq := fun _ e => e.elim
    qs_conj := fun _ e => e.elim
    th := fun _ _ e => e.elim }

@[reducible] def ex : @NExp D.R D.host D.what₂ D.nfLL D.starLL D.LL0 D.nd (tw D C K) :=
  { D.nexp with
    Fm := fun _ _ _ => PUnit
    acgFm := fun _ _ _ => inferInstance
    modFmK := fun _ _ _ => inferInstance
    modFmO := fun _ _ _ => inferInstance
    towFm := fun _ _ _ => inferInstance
    fdFm := fun _ _ _ => inferInstance
    actG := fun _ _ _ => 1
    Bsup := fun _ _ _ => ⊤
    Dat := fun _ _ _ => Empty
    th := fun _ _ _ a => a.elim
    lev := fun _ _ _ a => a.elim
    thPsi := fun _ _ _ _ _ _ a => a.elim
    thPsi_one := fun _ _ _ _ a => a.elim
    thU := fun _ _ _ _ _ a => a.elim
    twPsi := fun _ _ _ _ _ => 0
    twPsi_one := fun _ _ _ _ _ => (TensorProduct.tmul_zero _ _).symm
    twDel := fun _ _ _ _ _ => 0
    thP := fun _ _ _ _ _ _ => 0
    hkF := fun _ _ _ _ _ => 1
    embB := fun _ _ _ => 0
    embB_inj := fun _ _ _ _ _ _ => rfl
    eH := fun _ _ _ => 1
    eH_idem := fun _ _ _ => mul_one _ }

include hs in

theorem isTripleFor_ex (ha' : IsGlobalArtin art') (hT : TameTie C art' D.nd.chiT) : IsTripleFor C art' (ex D C K) := by
  refine ⟨ha', fun i _ b => ?_, fun _ _ s => s.elim, fun _ _ _ x _ hx => (hx rfl).elim⟩
  refine ⟨⟨(rd D i).κ, GlobalTheory.GalChar.sideIso (rd D i).ι b, (rd D i).κ_alg,
    GlobalTheory.GalChar.sideIso_read (rd D i).read (rd_conj D hs i) b⟩, ⟨fun j => (K i).gal j b, fun j k hk v => ?_⟩,
    fun s => s.elim⟩
  obtain ⟨n, hn⟩ := (K i).gal j b
  exact ⟨_, Or.inr rfl, hT k v _ hk _ _ _ j n _ hn⟩

end Record



end GlobalTheory.Triple.Model

end
