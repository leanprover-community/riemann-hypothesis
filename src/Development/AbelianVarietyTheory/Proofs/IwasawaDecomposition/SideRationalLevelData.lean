import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgWeightContragredientExistsUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeSpacesOrthogonalOfClassSumInnerStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisFamilyLocalConditionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeEigensystemMultiplicitiesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisFamilyCrystallineWeightsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisFamilyHeckeCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisFamilyDeterminantStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisFamilyIrreducibleStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisFamilyPolarized
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisFamilyTraceFrobeniusStatement

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.AutReps

variable {M N : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]

theorem comap_ne_bot_iff {f : M →ₗ[ℂ] N} (hf : Function.Injective f) (A : Submodule ℂ N) :
    A.comap f ≠ ⊥ ↔ A ⊓ LinearMap.range f ≠ ⊥ := by
  rw [inf_comm, ← Submodule.map_comap_eq, not_iff_not]
  constructor
  · intro h; rw [h, Submodule.map_bot]
  · intro h
    exact Submodule.map_injective_of_injective hf (by rw [h, Submodule.map_bot])

theorem iSupIndep_comap {ι : Type} {f : M →ₗ[ℂ] N} (hf : Function.Injective f) {A : ι → Submodule ℂ N}
    (hA : iSupIndep A) : iSupIndep (fun i => (A i).comap f) := by
  intro i
  rw [disjoint_iff]
  apply le_bot_iff.mp
  intro x hx
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.mp hx
  have h3 : f x ∈ ⨆ j, ⨆ (_ : j ≠ i), A j := by
    have hle : (⨆ j, ⨆ (_ : j ≠ i), (A j).comap f) ≤ (⨆ j, ⨆ (_ : j ≠ i), A j).comap f := by
      apply iSup_le; intro j; apply iSup_le; intro hj
      exact Submodule.comap_mono (le_iSup₂_of_le j hj le_rfl)
    exact hle h2
  have h4 : f x ∈ A i ⊓ ⨆ j, ⨆ (_ : j ≠ i), A j := Submodule.mem_inf.mpr ⟨h1, h3⟩
  rw [disjoint_iff.mp (hA i)] at h4
  have : f x = 0 := (Submodule.mem_bot ℂ).mp h4
  exact (Submodule.mem_bot ℂ).mpr (hf (this.trans (map_zero f).symm))

theorem iSup_comap_eq_top {ι : Type} {f : M →ₗ[ℂ] N} (hf : Function.Injective f) {A : ι → Submodule ℂ N}
    (hA : ⨆ i, A i ⊓ LinearMap.range f = LinearMap.range f) : ⨆ i, (A i).comap f = ⊤ := by
  apply Submodule.map_injective_of_injective hf
  rw [Submodule.map_iSup, Submodule.map_top]
  simp_rw [Submodule.map_comap_eq]
  simpa only [inf_comm] using hA

end GlobalTheory.AutReps

theorem GlobalTheory.AutReps.mtReal_decomp : ∀ (D : D7) (μ : D.what₂.Tup) (j : ℕ) (Mr : MtReal D μ j), ∃ (ι : Type) (_ : Finite ι) (F : ι → Submodule ℂ (GAf D.host.E D.R.nV → Mr.wt.W)), (∀ P, NG.IsIrrRep Mr.wt.ρ (F P)) ∧ (∀ P P', NG.IsoRep (F P) (F P') → P = P') ∧ (∀ S', NG.IsIrrRep Mr.wt.ρ S' → (NG.isoTyp Mr.wt.ρ S').comap Mr.real ≠ ⊥ → ∃ P, NG.IsoRep (F P) S') ∧ (∀ P, (NG.isoTyp Mr.wt.ρ (F P)).comap Mr.real ≠ ⊥) ∧ iSupIndep (fun P => (NG.isoTyp Mr.wt.ρ (F P)).comap Mr.real) ∧ ⨆ P, (NG.isoTyp Mr.wt.ρ (F P)).comap Mr.real = ⊤ := by
  intro D μ j Mr
  obtain ⟨_, ι, hι, S, hirr, hinj, hsurj, hne, hind, hsup⟩ :=
    GlobalTheory.T.typeSpaces_orthogonal_of_classSum_inner D.host.E D.R.nV Mr.wt Mr.J Mr.χ Mr.J_open
  have hR := Mr.real_range
  refine ⟨ι, hι, S, hirr, hinj, ?_, ?_, ?_, ?_⟩
  · intro S' h1 h2
    apply hsurj S' h1
    rw [← hR]; exact (GlobalTheory.AutReps.comap_ne_bot_iff Mr.real_inj _).mp h2
  · intro P
    rw [GlobalTheory.AutReps.comap_ne_bot_iff Mr.real_inj, hR]; exact hne P
  · exact GlobalTheory.AutReps.iSupIndep_comap Mr.real_inj hind
  · apply GlobalTheory.AutReps.iSup_comap_eq_top Mr.real_inj
    rw [hR]; exact hsup
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraicModularForms_irreducible_decomposition : ∀ (D : D7) (μ : D.what₂.Tup) (j : ℕ) (Mr : MtReal D μ j), ∃ (ι : Type) (_ : Finite ι) (F : ι → Submodule ℂ (GAf D.host.E D.R.nV → Mr.wt.W)), (∀ P, NG.IsIrrRep Mr.wt.ρ (F P)) ∧ (∀ P P', NG.IsoRep (F P) (F P') → P = P') ∧ (∀ S', NG.IsIrrRep Mr.wt.ρ S' → (NG.isoTyp Mr.wt.ρ S').comap Mr.real ≠ ⊥ → ∃ P, NG.IsoRep (F P) S') ∧ (∀ P, (NG.isoTyp Mr.wt.ρ (F P)).comap Mr.real ≠ ⊥) ∧ iSupIndep (fun P => (NG.isoTyp Mr.wt.ρ (F P)).comap Mr.real) ∧ ⨆ P, (NG.isoTyp Mr.wt.ρ (F P)).comap Mr.real = ⊤ := by
  atlas_forward_decl GlobalTheory.AutReps.mtReal_decomp
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_family_polarized : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hCS : ChoiceSide D cf M Bs.exp C tp) (hMI : MtInput D M tp.tup C.Q) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (hE : ∀ j g, ∃ z : ℤ, eExp D j g = z) (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) (hCh : GlobalTheory.RowTie.ChebSplit D.nd) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc) (ι : Type) [Finite ι] (F : ι → Submodule ℂ (GAf D.host.E D.R.nV → (mlX M X i).wt.W)) (irr : ∀ P, NG.IsIrrRep (mlX M X i).wt.ρ (F P)) (hinj : ∀ P P', NG.IsoRep (F P) (F P') → P = P') (hsurj : ∀ S', NG.IsIrrRep (mlX M X i).wt.ρ S' → (NG.isoTyp (mlX M X i).wt.ρ S').comap (mlX M X i).real ≠ ⊥ → ∃ P, NG.IsoRep (F P) S') (hne : ∀ P, (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real ≠ ⊥) (hind : iSupIndep (fun P => (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real)) (htop : ⨆ P, (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real = ⊤) (P : ι) (w : PlE D.host), ¬ IsSplitPl D.host w → D.nbc.sphAU (X.nd.j i) (A.au.cls (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2 { (mlX M X i).wt with S := F P, irrS := irr P }) w := by
  first | exact @GlobalTheory.SphNonSplit.sphAU_of_not_split | exact GlobalTheory.SphNonSplit.sphAU_of_not_split | (intros; apply GlobalTheory.SphNonSplit.sphAU_of_not_split <;> assumption)
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

open Classical in

noncomputable def GlobalTheory.AutPart.jumpOf (a : ℕ) (z : ℂ) : ℤ :=
  if h : ∃ n : ℤ, z = (n : ℂ) + ((a : ℂ) - 1) / 2 then -h.choose else 0

theorem GlobalTheory.AutPart.jumpOf_spec (a : ℕ) (z : ℂ) (h : ∃ n : ℤ, z = (n : ℂ) + ((a : ℂ) - 1) / 2) :
    ((GlobalTheory.AutPart.jumpOf a z : ℤ) : ℂ) = -z + ((a : ℂ) - 1) / 2 := by
  unfold GlobalTheory.AutPart.jumpOf
  rw [dif_pos h]
  conv_rhs => rw [h.choose_spec]
  push_cast; ring

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem GlobalTheory.AutPart.exists_autSpec : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → (∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → (tp.psi w).ValuesIn 0 D.what₂.embLL) → ∀ (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T), ∃ (Y : LocAut X) (Cb : LocBC Y), Nonempty (AutSpec A M tp.tup Sp.iq Y Cb) := by
  intro hArt D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh hψ big X T Sp
  classical
  choose ι hfin F hF using fun i : X.nd.Loc => GlobalTheory.T.algebraicModularForms_irreducible_decomposition D (X.nd.mu i) (X.nd.j i) (mlX M X i)
  have irr : ∀ i P, NG.IsIrrRep (mlX M X i).wt.ρ (F i P) := fun i => (hF i).1
  have hinj := fun i => (hF i).2.1
  have hsurj := fun i => (hF i).2.2.1
  have hne := fun i => (hF i).2.2.2.1
  have hind := fun i => (hF i).2.2.2.2.1
  have htop := fun i => (hF i).2.2.2.2.2
  obtain ⟨ptV, hptV⟩ : ∃ ptV : ∀ i, ι i → Option (X.nd.X i), ∀ i P x, ptV i P = some x ↔
      (∀ (w : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), SplitOut X.nd i w → IsConjPl D.host w s.w → IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ D.R.nV → ∀ y ∈ ((NG.isoTyp (mlX M X i).wt.ρ (F i P)).comap (mlX M X i).real), NG.tN (mlX M X i).J s ϖ k ((mlX M X i).real y) = (((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp (Sp.iq i)).comp (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)))) ((X.nd.hT i w k : X.nd.X i → X.nd.O i) x) • (mlX M X i).real y) := by
    refine ⟨fun i P => if h : ∃ x, (∀ (w : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), SplitOut X.nd i w → IsConjPl D.host w s.w → IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ D.R.nV → ∀ y ∈ ((NG.isoTyp (mlX M X i).wt.ρ (F i P)).comap (mlX M X i).real), NG.tN (mlX M X i).J s ϖ k ((mlX M X i).real y) = (((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp (Sp.iq i)).comp (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)))) ((X.nd.hT i w k : X.nd.X i → X.nd.O i) x) • (mlX M X i).real y) then some h.choose else none, fun i P x => ?_⟩
    dsimp only
    by_cases h : ∃ x, (∀ (w : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), SplitOut X.nd i w → IsConjPl D.host w s.w → IsUnif D.host.E s.v ϖ → 1 ≤ k → k ≤ D.R.nV → ∀ y ∈ ((NG.isoTyp (mlX M X i).wt.ρ (F i P)).comap (mlX M X i).real), NG.tN (mlX M X i).J s ϖ k ((mlX M X i).real y) = (((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp (Sp.iq i)).comp (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)))) ((X.nd.hT i w k : X.nd.X i → X.nd.O i) x) • (mlX M X i).real y)
    · rw [dif_pos h]
      constructor
      · rintro ⟨⟩; exact h.choose_spec
      · intro hx
        rw [GlobalTheory.T.galois_family_local_condition D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh big X T Sp i _ (hne i P) _ _ h.choose_spec hx]
    · rw [dif_neg h]
      exact ⟨fun h' => absurd h' (by simp), fun hx => (h ⟨x, hx⟩).elim⟩
  have hpts := fun i => haveI := hfin i; GlobalTheory.T.galois_family_unramified_outside D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh big X T Sp i (ι i) (F i) (irr i) (hinj i) (hsurj i) (hne i) (hind i) (htop i) (ptV i) (hptV i)
  choose μ hμc hμ using GlobalTheory.T.galois_family_crystalline_weights D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh big X T Sp
  choose κ hκ using GlobalTheory.T.galois_family_determinant D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh big X T Sp
  choose b hb using fun i : X.nd.Loc => GlobalTheory.algWt_contragredient D.host.E D.R.nV (mlX M X i).wt
  have hralg : ∀ {a} (π : D.naut.CG a) τ, D.naut.ralg π → ∀ z ∈ D.naut.infG π τ, ∃ n : ℤ, z = (n : ℂ) + ((a : ℂ) - 1) / 2 :=
    fun π τ h => ((D.naut.ralg_def π).1 h τ).2
  refine ⟨{
    iotaQ := Sp.iq
    iotaQC := fun i => (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i)))
    iota_LL := Sp.iq_LL
    iotaQ_alg := Sp.iq_alg
    muC := μ
    muC_csd := hμc
    AV := ι
    finAV := hfin
    ptV := ptV
    typeV := fun i P => ((NG.isoTyp (mlX M X i).wt.ρ (F i P)).comap (mlX M X i).real)
    typeV_ne := hne
    typeV_indep := hind
    typeV_top := htop
    pt_surj := fun i => (hpts i).1
    eig_dim := fun i => (hpts i).2
    locV := fun i P w => D.nbc.locAU (X.nd.j i) (A.au.cls (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2 { (mlX M X i).wt with S := F i P, irrS := irr i P }) w
    satV := fun i P w => D.nbc.satAU (X.nd.j i) (A.au.cls (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2 { (mlX M X i).wt with S := F i P, irrS := irr i P }) w
    locV_unr := fun i P w => haveI := hfin i; GlobalTheory.T.galois_family_irreducible D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh big X T Sp i (ι i) (F i) (irr i) (hinj i) (hsurj i) (hne i) (hind i) (htop i) P w
    pt_loc := fun i P x hx w hw => haveI := hfin i; GlobalTheory.T.galois_family_trace_frobenius D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh big X T Sp i (ι i) (F i) (irr i) (hinj i) (hsurj i) (hne i) (hind i) (htop i) (ptV i) (hptV i) P x hx w hw
    infWt := fun i => D.nbc.infW (X.nd.j i) (A.au.clsWt (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2 (b i))
    locW := fun i σ w => A.row.locR σ w
    satW := fun i σ w => A.row.satR σ w
    lab_loc := fun i k σ v => A.row.lab_eq k σ v
    wdOf := fun i {a} r w => A.wd.wdOf (X.nd.l i) (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) r w
    wdOf_dim := fun i {a} r w => A.wd.wdOf_dim (X.nd.l i) (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) r w
    wdOf_unr := fun i {a} r w => A.wd.wdOf_unr (X.nd.l i) (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) r w
    wdOf_frob := fun i {a} r w => A.wd.wdOf_frob (X.nd.l i) (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) r w
    wdOf_ine := fun i {a} r w => A.wd.wdOf_ine (X.nd.l i) (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) r w
    wdOf_mono0 := fun i {a} r w => A.wd.wdOf_mono0 (X.nd.l i) (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) r w
    IsCrysW := fun i {a} r w => A.wd.IsCrysW (X.nd.l i) (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) r w
    IsPotCrysW := fun i {a} r w => A.wd.IsPotCrysW (X.nd.l i) (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) r w
    IsdRW := fun i {a} r w => A.wd.IsdRW (X.nd.l i) (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) r w
    jumpsW := fun i {a} r τ => A.wd.jumpsW (X.nd.l i) (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) r τ
    wdOf_unrL := fun i {a} r w => A.wd.wdOf_unrL (X.nd.l i) (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) r w
    wdOf_mono0L := fun i {a} r w => A.wd.wdOf_mono0L (X.nd.l i) (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) r w
    jumpsInf := fun i {a} π τ => (D.naut.infG π ((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp τ)).map (GlobalTheory.AutPart.jumpOf a)
    locAutHodgeTateWeightsLevelZero := fun i τ => (D.nbc.infW (X.nd.j i) (A.au.clsWt (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2 (b i))
      ((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp τ)).map (GlobalTheory.AutPart.jumpOf D.R.nV)
    jumpsInf_def := fun i {a} π τ h => by
      rw [Multiset.map_map]
      exact Multiset.map_congr rfl fun z hz => GlobalTheory.AutPart.jumpOf_spec a z (hralg π _ h z hz)
    locAut_hodgeTateWeightsLevelZero_def := fun i τ => by
      rw [Multiset.map_map]
      exact Multiset.map_congr rfl fun z hz => GlobalTheory.AutPart.jumpOf_spec _ z ((D.nbc.infW_alg _ _ _).2 z hz)
    chi_mu := fun i w hw => GlobalTheory.T.galois_family_hecke_compatible hArt D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh hψ big X T Sp i (μ i) (hμc i) (hμ i) w hw
    kFbar := κ }, {
    embAV := fun i P => (A.au.cls (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2 { (mlX M X i).wt with S := F i P, irrS := irr i P })
    embAV_inj := fun i P P' h => hinj i P P' ((A.au.iso _ _ _ _ _).1 h).2
    embAV_loc := fun _ _ _ => rfl
    embAV_sat := fun _ _ _ => rfl
    embAV_sph := fun i P w hw => haveI := hfin i; GlobalTheory.T.galois_family_polarized D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh big X T Sp i (ι i) (F i) (irr i) (hinj i) (hsurj i) (hne i) (hind i) (htop i) P w hw
    embAV_inf := fun i P => by
      exact (congrArg (D.nbc.infW (X.nd.j i)) (A.au.wt _ _ _ _ (b i) (hb i).1)).symm }, ⟨{
    iotaQ := fun _ => rfl
    iotaQC := fun _ => rfl
    kFbar := hκ
    locW := fun _ _ _ => rfl
    satW := fun _ _ _ => rfl
    wdOf := fun _ _ _ _ => ⟨rfl, Iff.rfl, Iff.rfl, Iff.rfl, fun _ => rfl⟩
    muC := hμ
    S := F
    irr := irr
    inj := hinj
    surj := hsurj
    typeV := fun _ _ => rfl
    ptV := hptV
    emb := fun _ _ => rfl }⟩⟩
end
