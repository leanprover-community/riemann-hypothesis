import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowSetFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SplitOffDetection
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.HkSupSizedOfHkSup
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeValueIntegrality
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGoodRowHeckeOfOcc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemBlockTriangularTwoBlockSizesOfLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadWMemGoodW
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodLineIffEigenSpanStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenSpanInclusionInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHeckeDataSplitPlaceStatement

section
section
namespace GlobalTheory

open Module

theorem descent_joint_eigen : ∀ {K V W ι κ : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W] (f : K →+* ℂ) (e : V →ₛₗ[f] W) (G : Submodule K V), (∀ v ∈ G, e v = 0 → v = 0) → ∀ (T : κ → Module.End K V) (T' : κ → Module.End ℂ W) (I : Set κ), (∀ k ∈ I, ∀ v, e (T k v) = T' k (e v)) → ∀ (Part : ι → Submodule ℂ W) (s : Set ι) (lam : ι → κ → K), (∀ σ ∈ s, ∀ k ∈ I, ∀ w ∈ Part σ, T' k w = f (lam σ k) • w) → (∀ v, e v ∈ ⨆ σ ∈ s, Part σ → v ∈ G) → ∀ v, e v ∈ ⨆ σ ∈ s, Part σ → v ∈ ⨆ σ ∈ s, G ⊓ ⨅ k ∈ I, Module.End.eigenspace (T k) (lam σ k) := by
  classical
  intro K V W ι κ _ _ _ _ _ f e G hinj T T' I hT Part s lam hPart hG v hv
  set M := ⨆ σ ∈ s, G ⊓ ⨅ k ∈ I, Module.End.eigenspace (T k) (lam σ k) with hM
  have mono : ∀ S : Finset ι, (↑S : Set ι) ⊆ s → (⨆ σ ∈ S, Part σ) ≤ ⨆ σ ∈ s, Part σ := by
    intro S hS
    exact iSup₂_le fun σ hσ => le_iSup₂_of_le (f := fun σ (_ : σ ∈ s) => Part σ) σ (hS hσ) le_rfl
  have key : ∀ (S S'' : Finset ι), (↑S : Set ι) ⊆ s → ∀ k ∈ I, ∀ c : K,
      (∀ σ ∈ S, σ ∉ S'' → lam σ k = c) → ∀ v, e v ∈ ⨆ σ ∈ S, Part σ →
      e (T k v - c • v) ∈ ⨆ σ ∈ S'', Part σ := by
    intro S S'' hS k hk c hc v hv
    have hrw : e (T k v - c • v) = (T' k - f c • (1 : Module.End ℂ W)) (e v) := by
      simp [map_sub, hT k hk, LinearMap.map_smulₛₗ]
    rw [hrw]
    suffices h : (⨆ σ ∈ S, Part σ) ≤ (⨆ σ ∈ S'', Part σ).comap (T' k - f c • (1 : Module.End ℂ W)) from h hv
    refine iSup₂_le fun σ hσ w hw => ?_
    rw [Submodule.mem_comap, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
      hPart σ (hS hσ) k hk w hw, ← sub_smul]
    by_cases h : σ ∈ S''
    · exact Submodule.smul_mem _ _ (Submodule.mem_iSup_of_mem σ (Submodule.mem_iSup_of_mem h hw))
    · rw [hc σ hσ h, sub_self, zero_smul]; exact Submodule.zero_mem _
  have main : ∀ n : ℕ, ∀ S : Finset ι, S.card ≤ n → (↑S : Set ι) ⊆ s → ∀ v, e v ∈ ⨆ σ ∈ S, Part σ → v ∈ M := by
    intro n
    induction n with
    | zero =>
      intro S hS hSs v hv
      have hS0 : S = ∅ := Finset.card_eq_zero.mp (by omega)
      subst hS0
      simp only [Finset.notMem_empty, iSup_false, iSup_bot, Submodule.mem_bot] at hv
      have hvG : v ∈ G := hG v (by rw [hv]; exact Submodule.zero_mem _)
      rw [hinj v hvG hv]; exact Submodule.zero_mem _
    | succ n ih =>
      intro S hS hSs v hv
      rcases S.eq_empty_or_nonempty with hS0 | ⟨a, ha⟩
      · exact ih S (by simp [hS0]) hSs v hv
      by_cases hall : ∀ b ∈ S, ∀ k ∈ I, lam b k = lam a k
      · have hvG : v ∈ G := hG v (mono S hSs hv)
        have heig : v ∈ ⨅ k ∈ I, Module.End.eigenspace (T k) (lam a k) := by
          refine Submodule.mem_iInf _ |>.mpr fun k => Submodule.mem_iInf _ |>.mpr fun hk => ?_
          have h0 := key S ∅ hSs k hk (lam a k) (fun σ hσ _ => hall σ hσ k hk) v hv
          simp only [Finset.notMem_empty, iSup_false, iSup_bot, Submodule.mem_bot] at h0
          have hmG : T k v - lam a k • v ∈ G := hG _ (by rw [h0]; exact Submodule.zero_mem _)
          have := hinj _ hmG h0
          rw [Module.End.mem_eigenspace_iff]
          exact sub_eq_zero.mp this
        exact Submodule.mem_iSup_of_mem a (Submodule.mem_iSup_of_mem (hSs ha) (Submodule.mem_inf.mpr ⟨hvG, heig⟩))
      · push_neg at hall
        obtain ⟨b, hb, k, hk, hne⟩ := hall
        have hcb := Finset.card_erase_of_mem hb
        have hca := Finset.card_erase_of_mem ha
        have hsub : ∀ x, (↑(S.erase x) : Set ι) ⊆ s := fun x y hy => hSs (Finset.mem_of_mem_erase hy)
        have h1 := ih (S.erase b) (by omega) (hsub b) _
          (key S (S.erase b) hSs k hk (lam b k) (fun σ hσ hn => by
            by_contra hc; exact hn (Finset.mem_erase.mpr ⟨fun h => hc (h ▸ rfl), hσ⟩)) v hv)
        have h2 := ih (S.erase a) (by omega) (hsub a) _
          (key S (S.erase a) hSs k hk (lam a k) (fun σ hσ hn => by
            by_contra hc; exact hn (Finset.mem_erase.mpr ⟨fun h => hc (h ▸ rfl), hσ⟩)) v hv)
        have hv' : v = (lam a k - lam b k)⁻¹ • ((T k v - lam b k • v) - (T k v - lam a k • v)) := by
          rw [sub_sub_sub_cancel_left, ← sub_smul, smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hne.symm), one_smul]
        rw [hv']; exact M.smul_mem _ (M.sub_mem h1 h2)

  have hv2 : e v ∈ ⨆ σ, ⨆ (_ : σ ∈ s), Part σ := hv
  obtain ⟨S, hS⟩ := Submodule.mem_iSup_iff_exists_finset.mp hv2
  have hle : (⨆ σ ∈ S, ⨆ (_ : σ ∈ s), Part σ) ≤ ⨆ σ ∈ S.filter (· ∈ s), Part σ :=
    iSup₂_le fun σ hσ => iSup_le fun hs =>
      le_iSup₂_of_le (f := fun σ (_ : σ ∈ S.filter (· ∈ s)) => Part σ) σ (Finset.mem_filter.mpr ⟨hσ, hs⟩) le_rfl
  exact main _ _ le_rfl (fun x hx => (Finset.mem_filter.mp hx).2) v (hle hS)

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.descent_joint_eigenvectors_complex_reading : ∀ {K V W ι κ : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W] (f : K →+* ℂ) (e : V →ₛₗ[f] W) (G : Submodule K V), (∀ v ∈ G, e v = 0 → v = 0) → ∀ (T : κ → Module.End K V) (T' : κ → Module.End ℂ W) (I : Set κ), (∀ k ∈ I, ∀ v, e (T k v) = T' k (e v)) → ∀ (Part : ι → Submodule ℂ W) (s : Set ι) (lam : ι → κ → K), (∀ σ ∈ s, ∀ k ∈ I, ∀ w ∈ Part σ, T' k w = f (lam σ k) • w) → (∀ v, e v ∈ ⨆ σ ∈ s, Part σ → v ∈ G) → ∀ v, e v ∈ ⨆ σ ∈ s, Part σ → v ∈ ⨆ σ ∈ s, G ⊓ ⨅ k ∈ I, Module.End.eigenspace (T k) (lam σ k) := by
  atlas_forward_decl GlobalTheory.descent_joint_eigen
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.RecTie Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.RatSide
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EigSpanDesc

section Core

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem spanC_core (R : RealDat3 D A3 Ks) (F : Face3 D A3) {X0 : BaseLevelRowSide D} (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0)
    (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (kKs : Ks →+* ↥D.LL0)
    (hk : ∀ x : Ks, ((kKs x : ↥D.LL0) : D.what₂.LL) = algebraMap Ks D.what₂.LL x) (Sb : Finset (PlE D.host))
    (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ)
    (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL ((ratDatR R cG kKs hk).WL j))
    (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0)
    (hI : Rows.IsotInternal D.what₂) (hG : GlobalTheory.EigRows.OccGood D)
    (htie : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ v : (ratDatR R cG kKs hk).WL j, v ∈ goodL D (ratDatR R cG kKs hk) θ j ↔
      iotaR R (idxOf D j) v ∈ GlobalTheory.EigRows.goodW R.toRealDat F.lv2 (idxOf D j))
    (hinj : ∀ i, Function.Injective (iotaR R i))
    (hhk : ∀ (i : Fin D.R.m) (k : ℕ) (Pl : PlE D.host), 1 ≤ k → k ≤ D.R.r → IsSplitPl D.host Pl → Pl ∉ Sb →
      ∃ α Rr, HkDat R Sb i k Pl α Rr)
    (hRd : HeckeRd R cG kKs hk Sb hL) (hEig : EigAd Y Sb eig) :
    SpanC (ratDatR R cG kKs hk) Sb θ hL eig := by
  intro j hj1 hj2
  classical
  have hjj : ((idxOf D j : Fin D.R.m) : ℕ) + 1 = j := by
    show min (j - 1) (D.R.m - 1) + 1 = j
    omega
  have hsg : ∀ c : D.what₂.LL, D.what₂.embLL c = sg0 D A3.A c := fun c =>
    (congrArg (fun g : D.what₂.LL →+* ℂ => g c) (GlobalTheory.SeriesTie.ActProof.sg0_eq_embLL R)).symm
  let I : Set (ℕ × PlE D.host) := {t | 1 ≤ t.1 ∧ t.1 ≤ D.R.r ∧ IsSplitPl D.host t.2 ∧ t.2 ∉ Sb}
  have ex : ∀ t : I, ∃ α Rr, HkDat R Sb (idxOf D j) t.1.1 t.1.2 α Rr := fun t =>
    hhk (idxOf D j) t.1.1 t.1.2 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2
  choose α Rr hD using ex
  let T' : ℕ × PlE D.host → Module.End ℂ (Formalism.IndefR.Mult.MMap (R.MW (idxOf D j) (sg0 D A3.A))) := fun t =>
    if h : t ∈ I then hkNorm R (idxOf D j) t.1 t.2 • Formalism.IndefR.Mult.heckeOn (R.MW (idxOf D j) (sg0 D A3.A)) (Rr ⟨t, h⟩)
    else 0
  let Part : D.what₂.FT → Submodule ℂ (Formalism.IndefR.Mult.MMap (R.MW (idxOf D j) (sg0 D A3.A))) := fun σ =>
    (D.what₂.isot ((idxOf D j : ℕ) + 1) σ).map (GlobalTheory.EigRows.readW Y (idxOf D j))
  let s : Set D.what₂.FT := {σ | D.what₂.isot j σ ≠ ⊥ ∧ D.nd.goodRow σ}
  have hT : ∀ t ∈ I, ∀ u : Fin (R.nW (idxOf D j)) → D.what₂.LL,
      iotaR R (idxOf D j) (hL j t.1 t.2 u) = T' t (iotaR R (idxOf D j) u) := by
    intro t ht u
    simp only [T', dif_pos ht, LinearMap.smul_apply, iotaR_apply]
    exact hRd j t.1 t.2 (α ⟨t, ht⟩) (Rr ⟨t, ht⟩) hj1 hj2 (hD ⟨t, ht⟩) u
  have hPa : ∀ σ ∈ s, ∀ t ∈ I, ∀ z ∈ Part σ, T' t z = sg0 D A3.A ((eig j σ t.1 t.2 : ↥D.LL0) : D.what₂.LL) • z := by
    rintro σ hσ t ht _ ⟨y, hy, rfl⟩
    simp only [T', dif_pos ht, LinearMap.smul_apply]
    have h1 := hEig (idxOf D j) σ t.1 t.2 (α ⟨t, ht⟩) (Rr ⟨t, ht⟩) (hD ⟨t, ht⟩) hσ.2 y hy
    have h2 : eig ((idxOf D j : ℕ) + 1) σ t.1 t.2 = eig j σ t.1 t.2 := by rw [hjj]
    rw [h2, hsg] at h1
    exact h1
  have hGa : ∀ u, iotaR R (idxOf D j) u ∈ ⨆ σ ∈ s, Part σ → u ∈ goodL D (ratDatR R cG kKs hk) θ j := by
    intro u hu
    refine (htie j hj1 hj2 u).2 ?_
    have hle : (⨆ σ ∈ s, Part σ) ≤ GlobalTheory.EigRows.goodW R.toRealDat F.lv2 (idxOf D j) :=
      iSup₂_le fun σ _ => Submodule.map_le_iff_le_comap.2 fun y _ => readW_mem_goodW Y (idxOf D j) y
    exact hle hu
  intro v hv
  have hv' : iotaR R (idxOf D j) v ∈ ⨆ σ ∈ s, Part σ :=
    goodW_le_parts Y hI hG (idxOf D j) j hjj ((htie j hj1 hj2 v).1 hv)
  have hd := GlobalTheory.T.descent_joint_eigenvectors_complex_reading (sg0 D A3.A) (iotaR R (idxOf D j)) (goodL D (ratDatR R cG kKs hk) θ j)
    (fun u _ h0 => hinj (idxOf D j) (h0.trans (map_zero _).symm)) (fun t => hL j t.1 t.2) T' I hT Part s
    (fun σ t => ((eig j σ t.1 t.2 : ↥D.LL0) : D.what₂.LL)) hPa hGa v hv'
  have hle : (⨆ σ ∈ s, goodL D (ratDatR R cG kKs hk) θ j ⊓ ⨅ t ∈ I,
      Module.End.eigenspace (hL j t.1 t.2) ((eig j σ t.1 t.2 : ↥D.LL0) : D.what₂.LL)) ≤
      ⨆ σ ∈ {σ | D.what₂.isot j σ ≠ ⊥ ∧ D.nd.goodRow σ}, goodL D (ratDatR R cG kKs hk) θ j ⊓
        ⨅ (k : ℕ) (P : PlE D.host) (_ : 1 ≤ k ∧ k ≤ D.R.r ∧ IsSplitPl D.host P ∧ P ∉ Sb),
          Module.End.eigenspace (hL j k P) ((eig j σ k P : ↥D.LL0) : D.what₂.LL) :=
    iSup₂_mono fun σ _ => inf_le_inf_left _ (le_iInf fun k => le_iInf fun Pl => le_iInf fun h =>
      iInf₂_le (f := fun t (_ : t ∈ I) => Module.End.eigenspace (hL j t.1 t.2) ((eig j σ t.1 t.2 : ↥D.LL0) : D.what₂.LL))
        (k, Pl) h)
  exact hle hd

end Core

theorem spanC_of_state : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, StepW Start fun K B f T w => ∀ (P : Pre2 K w) (x : St P), LA hL x →
    Rows.IsotInternal (Dof x).what₂ → GlobalTheory.EigRows.OccGood (Dof x) →
    ∀ (θ : ∀ kk : Fin 2, Multiplicative (ZMod ((Dof x).host.g kk)) →* (↥(Dof x).LL0)ˣ)
      (hL' : ∀ j, ℕ → PlE (Dof x).host → Module.End (Dof x).what₂.LL ((SOf x).WL j)), (∀ kk, θ kk ≠ 1) →
      LvlPsi x.m.z.R x.m.z.F x.m.z.cG θ → StabC (SOf x) hL' → (∀ j Pl, hL' j 0 Pl = 1) →
      HeckeRd x.m.z.R x.m.z.cG (kKsOf x) (hkOf x) (SbD (Dof x)) hL' →
      ∀ eig : ℕ → (Dof x).what₂.FT → ℕ → PlE (Dof x).host → ↥(Dof x).LL0, EigAd x.r.Y (SbD (Dof x)) eig →
        SpanC (SOf x) (SbD (Dof x)) θ hL' eig := by
  intro hL
  refine (((GlobalTheory.T.good_line_iff_eigen_span hL).and (GlobalTheory.T.eigen_span_inclusion_injective hL)).and (GlobalTheory.T.exists_hecke_data_split_place hL)).trans (StepW.of_all fun K B f T w _ _ h => ?_)
  obtain ⟨⟨htie, hinj⟩, hhk⟩ := h
  intro P x hLA hI hG θ hL' hθ hlv _ _ hRd eig hEig
  exact spanC_core x.m.z.R x.m.z.F x.r.Y x.m.z.cG (kKsOf x) (hkOf x) (SbD (Dof x)) θ hL' eig hI hG
    (htie P x hLA θ hθ hlv) (hinj P x hLA) (hhk P x hLA) hRd hEig

end GlobalTheory.EigSpanDesc
end
end
